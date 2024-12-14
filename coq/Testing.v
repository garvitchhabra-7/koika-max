Require Import Koika.Frontend.
Require Import Coq.Program.Equality.
Require Koika.CompactLogs
        Koika.CompactSemantics.

Module CL := Koika.CompactLogs.
Module CS := Koika.CompactSemantics.

(* This dependently-typed function is required for the type of the context. *)
Definition input { sig : list (string * type) } := context ( fun (x : (string * type)) => type_denote (snd x) ) sig.
Notation "'assert' a ':=' b 'in' body" := (match b with | a => body | _ => False end) (at level 200, a pattern).

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
