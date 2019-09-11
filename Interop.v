Require Import Coq.Strings.String.
Require Import SGA.Environments SGA.Types SGA.Circuits SGA.Primitives.

Section Interop.
  Context {custom_ufn_t custom_fn_t: Type}.

  Inductive interop_ufn_t :=
  | UPrimFn (fn: prim_ufn_t)
  | UCustomFn (fn: custom_ufn_t).

  Inductive interop_fn_t :=
  | PrimFn (fn: prim_fn_t)
  | CustomFn (fn: custom_fn_t).

  Definition interop_Sigma
             (Sigma: custom_fn_t -> ExternalSignature)
    : interop_fn_t -> ExternalSignature  :=
    fun fn => match fn with
           | PrimFn fn => prim_Sigma fn
           | CustomFn fn => Sigma fn
           end.

  Definition interop_uSigma
             (uSigma: custom_ufn_t -> type -> type -> result custom_fn_t fn_tc_error)
             (fn: interop_ufn_t)
             (tau1 tau2: type)
    : result interop_fn_t fn_tc_error :=
    match fn with
    | UPrimFn fn => let/res fn := prim_uSigma fn tau1 tau2 in
                   Success (PrimFn fn)
    | UCustomFn fn => let/res fn := uSigma fn tau1 tau2 in
                     Success (CustomFn fn)
    end.

  Definition interop_sigma
             {Sigma: custom_fn_t -> ExternalSignature}
             (sigma: forall fn: custom_fn_t, Sigma fn)
    : forall fn: interop_fn_t, interop_Sigma Sigma fn :=
    fun fn => match fn with
           | PrimFn fn => prim_sigma fn
           | CustomFn fn => sigma fn
           end.
End Interop.

Inductive interop_empty_t :=.
Definition interop_empty_Sigma (fn: interop_empty_t)
  : ExternalSignature := match fn with end.
Definition interop_empty_uSigma (fn: interop_empty_t) (_ _: type)
  : result interop_empty_t fn_tc_error := match fn with end.
Definition interop_empty_sigma fn
  : interop_empty_Sigma fn := match fn with end.
Definition interop_empty_fn_names (fn: interop_empty_t)
  : string := match fn with end.

Record sga_package_t :=
  { (** [sga_reg_t]: The type of variables used in let bindings.
        Typically [string]. *)
    sga_var_t: Type;

    (** [sga_reg_t]: The type of registers used in the program.
        Typically an inductive [R0 | R1 | …] *)
    sga_reg_t: Type;
    (** [sga_reg_names]: These names are used to generate readable code. *)
    sga_reg_names: sga_reg_t -> string;
    (** [sga_reg_types]: The type of data stored in each register. *)
    sga_reg_types: sga_reg_t -> type;
    (** [sga_reg_types]: The type of data stored in each register. *)
    sga_reg_init: forall r: sga_reg_t, sga_reg_types r;
    (** [sga_reg_finite]: We need to be able to enumerate the set of registers
        that the program uses. *)
    sga_reg_finite: FiniteType sga_reg_t;

    (** [sga_custom_fn_t]: The type of custom functions used in the program.
        The [fn_t] used by the program itself should be [interop_fn_t
        sga_custom_fn_t], so the program can call primitives using (PrimFn …)
        and custom functions using (CustomFn …). *)
    sga_custom_fn_t: Type;
    (** [sga_custom_fn_t]: The signature of each function. *)
    sga_custom_fn_types: forall fn: sga_custom_fn_t, ExternalSignature;

    (** [sga_rule_name_t]: The type of rule names.
        Typically an inductive [rule1 | rule2 | …]. **)
    sga_rule_name_t: Type;
    (** [sga_rules]: The rules of the program. **)
    sga_rules: forall _: sga_rule_name_t,
        TypedSyntax.rule sga_var_t sga_reg_types (interop_Sigma sga_custom_fn_types);

    (** [sga_scheduler]: The scheduler. **)
    sga_scheduler: TypedSyntax.scheduler sga_rule_name_t;

    (** [sga_module_name]: The name of the current package. **)
    sga_module_name: string
  }.

Record circuit_package_t :=
  { cp_pkg: sga_package_t;

    (** [cp_reg_env]: This describes how the program concretely stores maps
        keyed by registers (this is used in the type of [cp_circuit], which is
        essentially a list of circuits, one per register. *)
    cp_reg_Env: Env cp_pkg.(sga_reg_t);

    (** [cp_circuit]: The actual circuit scheduler circuit generated by the
        compiler (really a list of circuits, one per register).  This should
        use [interop_fn_t cp_custom_fn_t] as the function type (and
        [interop_fn_Sigma cp_custom_fn_types] as the environment of
        signatures). *)
    cp_circuit: @state_transition_circuit
                  (cp_pkg.(sga_reg_t)) (@interop_fn_t cp_pkg.(sga_custom_fn_t))
                  (cp_pkg.(sga_reg_types)) (interop_Sigma cp_pkg.(sga_custom_fn_types))
                  cp_reg_Env;
  }.

Record verilog_package_t :=
  { vp_pkg: sga_package_t;

    (** [vp_custom_fn_names]: A map from custom functions to Verilog
        implementations. *)
    vp_custom_fn_names: forall fn: vp_pkg.(sga_custom_fn_t), string
  }.

Record sim_package_t :=
  { sp_pkg: sga_package_t;

    (** [sp_var_names]: These names are used to generate readable code. *)
    sp_var_names: sp_pkg.(sga_var_t) -> string;

    (** [sp_custom_fn_names]: A map from custom functions to C++
        implementations. *)
    sp_custom_fn_names: forall fn: sp_pkg.(sga_custom_fn_t), string;

    (** [sp_rule_names]: These names are used to generate readable code. **)
    sp_rule_names: sp_pkg.(sga_rule_name_t) -> string;

    (** [sp_extfuns]: A piece of C++ code implementing the custom external
        functions used by the program.  This is only needed if [sp_pkg] has a
        non-empty [sga_custom_fn_t].  It should implement a class called
        'extfuns', with public functions named consistently with
        [sp_custom_fn_names] **)
    sp_extfuns: option string
  }.

Definition compile_sga_package (s: sga_package_t) :=
  let FT := s.(sga_reg_finite) in
  {| cp_pkg := s;
     cp_circuit :=
       let R := s.(sga_reg_types) in
       let Sigma := interop_Sigma s.(sga_custom_fn_types) in
       let r := ContextEnv.(create) (readRegisters R Sigma) in
       compile_scheduler r s.(sga_rules) s.(sga_scheduler) |}.

Arguments interop_fn_t: clear implicits.
Arguments interop_ufn_t: clear implicits.

Definition interop_minimal_ufn_t := interop_ufn_t interop_empty_t.
Definition interop_minimal_fn_t := interop_fn_t interop_empty_t.
Definition interop_minimal_Sigma idx := interop_Sigma interop_empty_Sigma idx.
Definition interop_minimal_uSigma := interop_uSigma interop_empty_uSigma.
Definition interop_minimal_sigma := interop_sigma interop_empty_sigma.
