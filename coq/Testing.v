Require Import Koika.Frontend.
Require Import Coq.Program.Equality.
Require Koika.CompactLogs
        Koika.CompactSemantics.

Module CL := Koika.CompactLogs.
Module CS := Koika.CompactSemantics.

(* This dependently-typed function is required for the type of the context. *)
Definition input { sig : list (string * type) } := context ( fun (x : (string * type)) => type_denote (snd x) ) sig.
Notation "'assert' a ':=' b 'in' body" := (match b with | a => body | _ => False end) (at level 200, a pattern).

Notation "k := v" := (CtxCons (k, _) v CtxEmpty) (at level 200, only printing).
Notation "k := v ; ctx" := (CtxCons (k, _) v ctx) (at level 200, only printing).
Notation "{  gamma  } ⊢ rule —⟶ cont" := (interp_action_cps _ _ _ rule _ gamma _ cont) (at level 200, only printing).
Notation "{  gamma  } ⊢ rule —⟶ eval" := (interp_action _ _ gamma _ _ rule = eval) (at level 200, only printing).
Notation "{ }  ⊢ rule —⟶ cont" := (interp_action_cps _ _ _ rule _ CtxEmpty _ cont) (at level 200, only printing).
Notation "{ }  ⊢ rule —⟶ eval" := (interp_action _ _ CtxEmpty _ _ rule = eval) (at level 200, only printing).
Notation "'[' ']'" := log_empty (only printing).
Notation "a '<-' v '::' l" := (log_cons a v l) (at level 60, only printing).

Notation "'0d' num ':' sz" := (Bits.of_nat sz num) (at level 200, format "0d num : sz", only printing).

Section EvaluationUtilities.
  Context  [reg_t : Type ].
  Context `[FiniteType reg_t].
  Context  [R : reg_t -> type].
  Context  (r : (forall reg : reg_t, R reg)).
  Context  {tau : type}.

  Section Sigma.

    Context [ ext_fn_t : Type ].
    Context [ sigma : (ext_fn_t -> ExternalSignature) ].
    Context ( sigma_denote : (forall fn: ext_fn_t, Sig_denote (sigma fn)) ).

    (**
     * # run_function'
     *
     * This function can be used to compute a koika function.
     *
     * Note: It could also be used for actions, but we also provide
     *       [run_action'] to implicitly pass no function arguments.
     *
     * # Arguments
     *
     * - r            : register value assignment
     * - sigma_denote : coq implementations of external functions
     * - inputs       : direct inputs to the function
     * - func         : the actual koika function to run
     * - callback     : a callback function that is run on the
     *                  function's result if it didn't fail
     *
     * # Callback Arguments
     *
     * - ctxt : a koika context, holding the new register values
     * - out  : the direct output of the function
     *
     * # Examples
     *
     * see []()
     *)
    Definition run_function'
      [ sig : tsig var_t ]
      ( inputs : input )
      ( func : action R sigma sig tau )
      : option (ContextEnv.(env_t) R * tau) :=
        let env := ContextEnv.(create) r in
        option_map (fun '(log,out,_) => (commit_update env log, out))
          (interp_action env sigma_denote inputs log_empty log_empty func).

    (**
     * # run_funcion_cs'
     *
     * This is a compact sematics variant of [run_function']
     *)
    Definition run_function_cs'
      [ sig : tsig var_t ]
      ( inputs : input )
      ( func : action R sigma sig tau )
      : option (ContextEnv.(env_t) R * tau) :=
        let env := ContextEnv.(create) r in
        option_map (fun '(log,out,_) => (CL.commit_update env log, out))
          (CS.interp_action env sigma_denote inputs CL.log_empty CL.log_empty func).

    (**
     * # run_action'
     *
     * Utility function of [run_function']
     *
     * In contrast to [run_function'] this function does not expect a function input
     * this might be handy to test actions instead of functions.
     * Additionally, the callback does not provide an output, only a context.
     *
     * # Arguments
     *
     * see [run_function']
     *)
    Definition run_action' func :=
        option_map (fun '(ctxt,out) => ctxt)
          (run_function' CtxEmpty func).

    (**
     * # run_action_cs'
     *
     * This is a compact sematics variant of [run_action']
     *)
    Definition run_action_cs' func :=
        option_map (fun '(ctxt,out) => ctxt)
          (run_function_cs' CtxEmpty func).

    (**
     * # run_schedule
     *
     * This function can be used to compute a koika action or function
     *
     * # Arguments
     *
     * - r            : register value assignment
     * - rules        : mapping of rule names to actions
     * - sigma_denote : implementations of external functions
     * - sched        : the scheduler to run
     * - callback     : this function is invoked on the resulting
     *                  context
     *
     * # Callback Arguments
     *
     * - ctxt     : a koika context, holding new register values
     *
     * # Examples
     *
     * TODO
     *)
    Definition run_schedule
      [ rule_name_t ]
      ( rules : rule_name_t -> action R sigma [] unit_t )
      ( sched : scheduler )
      : ContextEnv.(env_t) R :=
        let env := ContextEnv.(create) r in
        let log := interp_scheduler env sigma_denote rules sched in
        (commit_update env log).

    (**
     * # run_schedule_cs
     *
     * This is a compact sematics variant of [run_schedule]
     *)
    Definition run_schedule_cs
      [ rule_name_t ]
      ( rules : rule_name_t -> action R sigma [] unit_t )
      ( sched : scheduler )
      : ContextEnv.(env_t) R :=
        let env := ContextEnv.(create) r in
        let log := CS.interp_scheduler env sigma_denote rules sched in
        (CL.commit_update env log).
  End Sigma.

  (**
  * # run_function
  *
  * Utility function of [run_function']
  *
  * In contrast to [run_function'] this expects an empty external function
  * signature.
  *
  * # Arguments
  *
  * see [run_function']
  *)
  Definition run_function [sig] :=
      run_function' empty_sigma (sig := sig).

  (**
   * # run_function_cs
   *
   * This is a compact sematics variant of [run_function]
   *)
  Definition run_function_cs [sig] :=
    run_function_cs' empty_sigma (sig := sig).

  (**
  * # run_action
  *
  * Utility function of [run_action']
  *
  * In contrast to [run_action'] this expects an empty external function
  * signature.
  *
  * # Arguments
  *
  * see [run_action']
  *)
  Definition run_action :=
      run_action' empty_sigma.

  (**
   * # run_action_cs
   *
   * This is a compact sematics variant of [run_action]
   *)
   Definition run_action_cs :=
    run_action_cs' empty_sigma.
End EvaluationUtilities.


Ltac check :=
  vm_compute; firstorder || match goal with
         | |- _ /\ _ => (split; check)
         | |- _ \/ _ => (left; check) || (right; check)
         | |- True => constructor
         | _ : False  |- _ => contradiction
         (* | |- ?A = ?B => fail "Assertion failure! The following equality does not hold: " A "=" B *)
         | |- ?ineq => idtac "Assertion failure! The following equality does not hold: " ineq
         end.


Ltac koika_unfold_eval :=
  repeat match goal with
  | |- context[run_function'] => unfold run_function'
  | |- context[run_function_cs'] => unfold run_function_cs'
  | |- context[run_action'] => unfold run_action'
  | |- context[run_action_cs'] => unfold run_action_cs'
  | |- context[run_schedule] => unfold run_schedule
  | |- context[run_schedule_cs] => unfold run_schedule_cs
  | |- context[run_function] => unfold run_function
  | |- context[run_function_cs] => unfold run_function_cs
  | |- context[run_action] => unfold run_action
  | |- context[run_action_cs] => unfold run_action_cs
  end.

Local Lemma option_map_some_spec [A B] (f : A -> B) a :
  option_map f (Some a) = Some (f a).
Proof. reflexivity. Qed.

Local Lemma option_map_map [A] o [B] (f1 : A -> B) [C] (f2 : B -> C) :
  option_map f2 (option_map f1 o) = option_map (fun a => f2 (f1 a)) o.
Proof. destruct o; reflexivity. Qed.

Ltac koika_start :=
  koika_unfold_eval;
  repeat match goal with
  | |- context[option_map _ (option_map _ _)] => rewrite option_map_map
  | |- context[@option_map ?Ta ?Tb _ ?x] =>
    (* I assume that x is an interp_action which returns a triple *)
    let H := fresh "H" in
    eassert (H : x = Some (_,_,_));
    [|rewrite H, option_map_some_spec; clear H]
  end.

Ltac koika_switch_to_cps :=
  match goal with
  | |- context[CS.interp_scheduler] => rewrite <- interp_scheduler_cps_correct
  | |- context[CS.interp_action] => rewrite <- interp_action_cps_correct
  end + fail "You need to use interp_action or interp_scheduler from the compact semantics".

Ltac koika_start_cps :=
  koika_start;
  try koika_switch_to_cps.

Local Lemma opt_bind_some [A B] (f : A -> option B) a b o :
  o = Some b -> f b = Some a ->
  opt_bind o f = Some a.
Proof. intros; rewrite H; assumption. Qed.

Ltac koika_unfold' :=
  match goal with
  | |- interp_action_cps _ _ _ (?rule) _ _ _ _ =>
    head_constructor rule;
    rewrite <- interp_action_cps_eqn;
    unfold interp_action_cps1
  | |- interp_action _ _ _ _ _ (?rule) = _ =>
    head_constructor rule;
    rewrite <- interp_action_eqn;
    unfold interp_action1
  end.

Ltac koika_unfold :=
  koika_unfold';
  repeat match goal with
  | |- opt_bind ?x _ = Some _ =>
    eapply (opt_bind_some _ _ (_,_,_))
  end.

Tactic Notation "rewrite_pat" constr(t) constr(re) :=
  remember t as Z eqn : HZ;
  rewrite re in HZ;
  subst Z.

Definition negb_true : negb true = false := eq_refl.
Definition negb_false : negb false = true := eq_refl.

Ltac bool_simpl' :=
  match goal with
  | |- context[orb ?a ?a] => rewrite orb_diag
  | |- context[andb ?a ?a] => rewrite andb_diag
  | |- context[orb ?a (negb ?a)] => rewrite orb_negb_r
  | |- context[orb (negb ?a) ?a] => rewrite orb_negb_r
  | |- context[andb ?a (negb ?a)] => rewrite andb_negb_r
  | |- context[andb (negb ?a) ?a] => rewrite andb_negb_l
  | |- context[andb ?a (orb ?a _)] => rewrite absorption_andb
  | |- context[orb ?a (andb ?a _)] => rewrite absorption_orb

  (* simplify using constants *)
  | |- context[andb false ?_a] => rewrite_pat (andb false _a) andb_false_r
  | |- context[andb ?_a false] => rewrite_pat (andb _a false) andb_false_l
  | |- context[orb true ?_a] => rewrite_pat (orb true _a) orb_true_l
  | |- context[orb ?_a true] => rewrite_pat (orb _a true) orb_true_r

  (* I would argue these rules do less simplification
    as they are only discarding a constant - so they are
    tried later *)
  | |- context[negb true] => rewrite_pat (negb true) negb_true
  | |- context[negb false] => rewrite_pat (negb false) negb_false

  | |- context[andb true _] => rewrite andb_true_r
  | |- context[andb _ true] => rewrite andb_true_l
  | |- context[orb false _] => rewrite orb_false_l
  | |- context[orb _ false] => rewrite orb_false_r

  (* lastly I try to dedup the goal as much as possible
    to make it more readable *)
  | |- context[orb _ (orb _ _)] => rewrite orb_assoc
  | |- context[andb _ (andb _ _)] => rewrite andb_assoc
  | |- context[negb (negb _)] => rewrite negb_involutive
  | |- context[andb (negb _) (negb _)] => rewrite <- negb_andb
  | |- context[orb  (negb _) (negb _)] => rewrite <- negb_orb
  | |- context[orb (andb ?a _) (andb ?a _)] => rewrite <- andb_orb_distrib_r
  | |- context[orb (andb _ ?a) (andb _ ?a)] => rewrite <- andb_orb_distrib_l
  | |- context[andb (orb ?a _) (orb ?a _)] => rewrite <- orb_andb_distrib_r
  | |- context[andb (orb _ ?a) (orb _ ?a)] => rewrite <- orb_andb_distrib_l
  end.

Import Koika.SemanticProperties.
Ltac log_simpl :=
  match goal with
  | |- context H [log_existsb log_empty _ _] =>  let x := context H [false] in change x (* rewrite log_existsb_empty *)
  | |- context[log_existsb (log_app _ _) _ _] => rewrite log_existsb_app
  | |- context[@log_existsb _ ?R _ (log_cons ?i _ _) ?i _] => rewrite (@log_existsb_log_cons_eq _ R)
  | |- context[log_existsb (log_cons _ _ _) _ _] => rewrite log_existsb_log_cons_neq by discriminate


  | |- context[latest_write (log_cons ?i _ _) ?i] => rewrite latest_write_cons_eq
  | |- context[latest_write0 (log_cons ?i _ _) ?i] => rewrite latest_write0_cons_eq
  | |- context[latest_write1 (log_cons ?i _ _) ?i] => rewrite latest_write1_cons_eq
  | |- context[latest_write (log_app _ _) _] => rewrite latest_write_app
  | |- context[latest_write0 (log_app _ _) _] => rewrite latest_write0_app
  | |- context[latest_write1 (log_app _ _) _] => rewrite latest_write1_app
  | |- context[may_read] => unfold may_read
  | |- context[may_write] => unfold may_write
  | |- context[is_read0 ?k ?p] => head_constructor k; head_constructor p; unfold is_read0
  | |- context[is_read1 ?k ?p] => head_constructor k; head_constructor p; unfold is_read1
  | |- context[is_write0 ?k ?p] => head_constructor k; head_constructor p; unfold is_write0
  | |- context[is_write1 ?k ?p] => head_constructor k; head_constructor p; unfold is_write1
  end.

Ltac ctx_simpl :=
  match goal with
  | |- context[getenv _ (commit_update _ _) _] => rewrite getenv_commit_update
  | |- context[getenv _ (create _ _)] => rewrite getenv_create
  | |- context[cassoc _ ?c] => head_constructor c; unfold cassoc
  | |- context[chd ?c] => head_constructor c; unfold chd
  | |- context[ctl ?c] => head_constructor c; unfold ctl
  end.
(*
Lemma if_some [A] c (a b : A) :
  c = true -> a = b ->
  (if c then Some a else None) = Some b.
Proof. intros H1 H2. rewrite H1, H2. auto. Qed. *)

Module PrS := PrimSpecs.
Module CPrS := CircuitPrimSpecs.


Ltac prim_simpl :=
  match goal with
  | |- context[PrS.sigma1] => unfold PrS.sigma1
  | |- context[PrS.sigma2] => unfold PrS.sigma2
  | |- context[CPrS.sigma1] => unfold CPrS.sigma1
  | |- context[CPrS.sigma2] => unfold CPrS.sigma2
  end.

Ltac koika_simpl' tac :=
  repeat match goal with
  | _ => tac
  (* use reflexivity as last step to ensure that the terms
    have been simplified as far as possible before being
    unified *)
  | |- Some (_,_,_) = Some (_,_,_) => reflexivity
  end.

Tactic Notation "koika_simpl" "[" tactic_list_sep(tac, ",") "]" :=
  koika_simpl' ltac:(first tac).

(* This tactic simplifies with a default set of tactics
  use `koika_simpl [...]` to simplify only with the specified
  set of tactics *)
Tactic Notation "koika_simpl" :=
  koika_simpl [bool_simpl', log_simpl, ctx_simpl, prim_simpl].

Tactic Notation "koika_step" :=
  koika_unfold; koika_simpl.

Tactic Notation "koika_step" "[" tactic_list_sep(tac, ",") "]" :=
  koika_unfold; koika_simpl' ltac:(first tac).
