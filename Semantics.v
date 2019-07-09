Require Import Coq.Lists.List.
Require Import SGA.Common SGA.Syntax SGA.Environments SGA.Types.

Import ListNotations.

Inductive value :=
| vtt
| vbits (val: bits).

Definition type_of_value (v: value) :=
  match v with
  | vtt => unit_t
  | vbits bs => bit_t (length bs)
  end.

Inductive result {A} :=
| Success (a: A)
| CannotRun
| Stuck.
Arguments result : clear implicits.

Definition result_bind {A B} (r: result A) (f: A -> result B) :=
  match r with
  | Success a => f a
  | CannotRun => CannotRun
  | Stuck => Stuck
  end.

Definition result_map {A B} (r: result A) (f: A -> B) :=
  result_bind r (fun a => Success (f a)).

Definition opt_result {A} (default: result A) (o: option A) :=
  match o with
  | Some a => Success a
  | None => default
  end.

Inductive LogEntryKind := LogRead | LogWrite.
Record LogEntry := LE
  { kind: LogEntryKind;
    level: Level;
    reg: nat;
    val: bits (* [] for reads *) }.

Definition Log := list LogEntry.

Record ExternalFunction :=
  ExtFun { sig: ExternalSignature;
           impl:> list bits -> value;
           type_ok: forall args: list bits,
               List.length args = List.length sig.(argSizes) ->
               type_of_value (impl args) = sig.(retType) }.

Require Import SGA.Environments SGA.Types.

Section Interp.
  Context {TVar: Type}.
  Context {TFn: Type}.

  Context {RegEnv: Env nat bits}.
  Context {SigmaEnv: Env TFn ExternalFunction}.
  Context {GammaEnv: Env TVar value}.
  Open Scope bool_scope.

  Definition log_find log reg (f: LogEntryKind -> Level -> bits -> bool) :=
    List.find (fun '(LE kind lvl r v) => if PeanoNat.Nat.eq_dec reg r then f kind lvl v else false) log.

  Definition log_forallb log reg (f: LogEntryKind -> Level -> bits -> bool) :=
    List.forallb (fun '(LE kind lvl r v) => if PeanoNat.Nat.eq_dec reg r then f kind lvl v else true) log.

  Definition bool_result (b: bool) : result unit :=
    if b then Success tt else CannotRun.

  Definition may_read0 sched_log rule_log idx :=
    (log_forallb sched_log idx
                 (fun kind lvl _ => match kind, lvl with
                                 | LogWrite, P0 => false
                                 | _, _ => true
                                 end)) &&
    (log_forallb (rule_log ++ sched_log) idx
                 (fun kind lvl _ => match kind, lvl with
                                 | _, P1 => false
                                 | _, _ => true
                                 end)).

  Definition may_read1 sched_log idx :=
    log_forallb sched_log idx
                (fun kind lvl _ => match kind, lvl with
                                | LogWrite, P1 => false
                                | _, _ => true
                                end).

  Definition latest_write0 log idx :=
    log_find log idx
             (fun kind lvl _ => match kind, lvl with
                             | LogWrite, P0 => true
                             | _, _ => false
                             end).

  Definition may_write sched_log rule_log lvl idx :=
    match lvl with
       | P0 => log_forallb (rule_log ++ sched_log) idx
                          (fun kind lvl _ => match kind, lvl with
                                          | LogRead, P1 | LogWrite, _ => false
                                          | _, _ => true
                                          end)
       | P1 => log_forallb (rule_log ++ sched_log) idx
                          (fun kind lvl _ => match kind, lvl with
                                          | LogWrite, P1 => false
                                          | _, _ => true
                                          end)
    end.

  Definition assert_size (bs: bits) (size: nat) : result bits :=
    if PeanoNat.Nat.eq_dec (List.length bs) size then Success bs
    else Stuck.

  Definition assert_bits (v: value) (size: nat) : result bits :=
    match v with
    | vbits bs => assert_size bs size
    | _ => Stuck
    end.


  Definition fold_left2_result
             {A B B': Type} (f: A -> B -> B' -> result A)
             (l: list B) (l': list B') (a0: A) : result A :=
    fold_left2 (fun acc b b' =>
                  result_bind acc (fun acc =>
                  f acc b b')) l l' (Success a0).

  Fixpoint interp_rule
           (V: RegEnv.(env_t))
           (Sigma: SigmaEnv.(env_t))
           (Gamma: GammaEnv.(env_t))
           (sched_log: Log)
           (rule_log: Log)
           (s: rule TVar TFn)
           {struct s} :=
    match s with
    | Bind var expr body =>
      result_bind (interp_rule V Sigma Gamma sched_log rule_log expr) (fun '(rule_log', v) =>
      interp_rule V Sigma (putenv Gamma var v) sched_log rule_log body)
    | Var var =>
      result_map (opt_result Stuck (getenv Gamma var)) (fun val => (rule_log, val))
    | Skip =>
      Success (rule_log, vtt)
    | Const cst =>
      Success (rule_log, vbits cst)
    | If cond tbranch fbranch =>
      result_bind (interp_rule V Sigma Gamma sched_log rule_log cond) (fun '(rule_log', condv) =>
      if condv
      then interp_rule V Sigma Gamma sched_log rule_log' tbranch
      else interp_rule V Sigma Gamma sched_log rule_log' fbranch)
    | Fail =>
      CannotRun
    | Read P0 idx =>
      result_bind (opt_result Stuck (getenv V idx)) (fun v =>
      result_map (bool_result (may_read0 sched_log rule_log idx)) (fun _ =>
      ((LE LogRead P0 idx []) :: rule_log, vbits v)))
    | Read P1 idx =>
      result_bind (opt_result Stuck (getenv V idx)) (fun bs0 =>
      result_bind (bool_result (may_read1 sched_log idx)) (fun _ =>
      result_map (match latest_write0 (rule_log ++ sched_log) idx with
                  | Some {| val := v |} => assert_size v (length bs0)
                  | None => Success bs0
                  end) (fun bs =>
      ((LE LogRead P1 idx []) :: rule_log, vbits bs))))
    | Write lvl idx val =>
      result_bind (opt_result Stuck (getenv V idx)) (fun bs0 =>
      result_bind (interp_rule V Sigma Gamma sched_log rule_log val) (fun '(rule_log, v) =>
      result_bind (bool_result (may_write sched_log rule_log lvl idx)) (fun _ =>
      result_map (assert_bits v (List.length bs0)) (fun bs =>
      ((LE LogWrite lvl idx bs) :: rule_log, vtt)))))
    | Call fn args =>
      result_bind (opt_result Stuck (getenv Sigma fn)) (fun fn =>
      if PeanoNat.Nat.eq_dec (List.length args) (List.length fn.(sig).(argSizes)) then
        result_map
          (fold_left2_result
             (fun '(rule_log, argvs) arg size =>
                result_bind (interp_rule V Sigma Gamma sched_log rule_log arg) (fun '(rule_log, argv) =>
                result_map (assert_bits argv size) (fun bs =>
                (rule_log, bs :: argvs))))
             args fn.(sig).(argSizes) (rule_log, []))
          (fun '(rule_log, argvs) => (rule_log, (fn argvs)))
      else Stuck)
    end.

  Fixpoint interp_scheduler
           (V: RegEnv.(env_t))
           (Sigma: SigmaEnv.(env_t))
           (sched_log: Log)
           (s: scheduler TVar TFn)
           {struct s} :=
    match s with
    | Done => Some sched_log
    | Try r s1 s2 =>
      match interp_rule V Sigma env_nil sched_log [] r with
      | Success (l, _) => interp_scheduler V Sigma (l ++ sched_log) s1
      | CannotRun => interp_scheduler V Sigma sched_log s2
      | Stuck => None
      end
    end.
End Interp.
