Require Import Bool.
Require Import HahnBase.
Require Import Heaps.
Require Import List.
Require Import Morphisms.
Require Import Permissions.
Require Import Prelude.
Require Import Setoid.

Import ListNotations.

Set Implicit Arguments.


(** * Programs *)

Module Type Programs
  (dom : Domains)
  (heaps : Heaps dom).

Export dom heaps.


(** ** Statics *)

(** *** Expressions *)

Inductive Expr :=
  | Econst(v : Val)
  | Evar(x : Var)
  | Eop(E1 E2 : Expr).

Add Search Blacklist "Expr_rect".
Add Search Blacklist "Expr_ind".
Add Search Blacklist "Expr_rec".
Add Search Blacklist "Expr_sind".

(** Below is a helper tactic for doing induction
    on the structure of (program) expressions. *)

Ltac expr_induction E :=
  induction E as [
    (* constants *)
    v|
    (* variables *)
    x|
    (* binary operations *)
    E1 IH1 E2 IH2
  ].

(** Expressions have decidable equality. *)

Lemma expr_eq_dec :
  forall E1 E2 : Expr, { E1 = E2 } + { E1 <> E2 }.
Proof.
  decide equality.
  - apply val_eq_dec.
  - apply var_eq_dec.
Qed.

(** **** Conversions *)

(** **** Free variables *)

(** Free variables of expressions are defined in the standard way. *)

Fixpoint expr_fv (E : Expr) : list Var :=
   match E with
    | Econst v => []
    | Evar x => [x]
    | Eop E1 E2 => expr_fv E1 ++ expr_fv E2
  end.

Definition expr_map_fv {T} (f : T -> Expr)(x : Var) : Prop :=
  exists t : T, In x (expr_fv (f t)).

(** **** Substitution *)

(** Substitution within expressions is defined in the standard way. *)

Fixpoint expr_subst (x : Var)(E E' : Expr) : Expr :=
  match E' with
    | Econst v => Econst v
    | Evar y => if var_eq_dec x y then E else Evar y
    | Eop E1 E2 => Eop (expr_subst x E E1) (expr_subst x E E2)
  end.

Definition expr_subst_map {T} (x : Var)(E : Expr)(f : T -> Expr) : T -> Expr :=
  fun y : T => expr_subst x E (f y).

(** Standard properties of substitution. *)

Lemma expr_subst_pres :
  forall E1 E2 x, ~ In x (expr_fv E1) -> expr_subst x E2 E1 = E1.
Proof.
  expr_induction E1; intros E x' H; simpls; intuition desf.
  rewrite IH1, IH2; auto.
  - intro H1. apply H. apply in_or_app. by right.
  - intro H1. apply H. apply in_or_app. by left.
Qed.

Lemma expr_subst_pres_map {T} :
  forall (f : T -> Expr) E x,
  ~ expr_map_fv f x -> expr_subst_map x E f = f.
Proof.
  intros f E x H1.
  extensionality t. apply expr_subst_pres.
  intro H2. apply H1. by exists t.
Qed.

Lemma expr_subst_comm :
  forall E x1 x2 E1 E2,
  x1 <> x2 ->
  ~ In x1 (expr_fv E2) ->
  ~ In x2 (expr_fv E1) ->
  expr_subst x1 E1 (expr_subst x2 E2 E) =
  expr_subst x2 E2 (expr_subst x1 E1 E).
Proof.
  expr_induction E; intros x1 x2 E1' E2' H1 H2 H3;
    simpl; vauto.
  (* variables *)
  - destruct (var_eq_dec x1 x), (var_eq_dec x2 x); vauto.
    + simpl. desf. by rewrite expr_subst_pres.
    + simpl. desf. by rewrite expr_subst_pres.
    + simpl. desf.
  (* operations *)
  - by rewrite IH1, IH2.
Qed.

Lemma expr_subst_comm_val :
  forall E x1 x2 v1 v2,
  x1 <> x2 ->
  expr_subst x1 (Econst v1) (expr_subst x2 (Econst v2) E) =
  expr_subst x2 (Econst v2) (expr_subst x1 (Econst v1) E).
Proof.
  intros E c1 c2 v1 v2 H1.
  by rewrite expr_subst_comm.
Qed.

(** *** Conditions *)

Inductive Cond :=
  | Bconst(b : bool)
  | Bnot(B : Cond)
  | Band(B1 B2 : Cond)
  | Beq(E1 E2 : Expr).

Add Search Blacklist "Cond_rect".
Add Search Blacklist "Cond_ind".
Add Search Blacklist "Cond_rec".
Add Search Blacklist "Cond_sind".

(** Below is a helper tactic for doing induction
    on the structure of (program) conditions. *)

Ltac cond_induction B :=
  induction B as [
    (* constant Booleans *)
    b|
    (* negation *)
    B IH|
    (* conjunction *)
    B1 IH1 B2 IH2|
    (* equality *)
    E1 E2
  ].

(** Conditions have decidable equality. *)

Lemma cond_eq_dec :
  forall B1 B2 : Cond, { B1 = B2 } + { B1 <> B2 }.
Proof.
  decide equality.
  - apply bool_dec.
  - apply expr_eq_dec.
  - apply expr_eq_dec.
Qed.

(** Some sugar *)

Definition Bor B1 B2 := Bnot (Band (Bnot B1) (Bnot B2)).
Definition Bimplies B1 B2 := Bor (Bnot B1) B2.
Definition Bequiv B1 B2 := Band (Bimplies B1 B2) (Bimplies B2 B1).


(** **** Free variables *)

(** Free variables of conditions are defined in the standard way. *)

Fixpoint cond_fv (B : Cond) : list Var :=
   match B with
    | Bconst b => nil
    | Bnot B' => cond_fv B'
    | Band B1 B2 => cond_fv B1 ++ cond_fv B2
    | Beq E1 E2 => expr_fv E1 ++ expr_fv E2
  end.

(** **** Substitution *)

(** Substitution within conditions is defined in the standard way. *)

Fixpoint cond_subst (x : Var)(E : Expr)(B : Cond) : Cond :=
  match B with
    | Bconst b => Bconst b
    | Bnot B' => Bnot (cond_subst x E B')
    | Band B1 B2 => Band (cond_subst x E B1) (cond_subst x E B2)
    | Beq E1 E2 => Beq (expr_subst x E E1) (expr_subst x E E2)
  end.

(** Standard properties of substitution. *)

Lemma cond_subst_pres :
  forall B E x, ~ In x (cond_fv B) -> cond_subst x E B = B.
Proof.
  cond_induction B; intros E x H; simpls.
  - by rewrite IH.
  - rewrite IH1, IH2; intuition.
  - repeat rewrite expr_subst_pres; intuition.
Qed.

(** *** Commands *)

(** Commands are parameterised by a type, which is the type of the
    metadata that is stored in action blocks (see the [Cinact] constructor).
    We later define a ghost operational semantics (in which the metadata
    component is used to maintain extra runtime information
    regarding abstract models. *)

Inductive Cmd (T : Type) :=
  | Cskip
  | Cseq(C1 C2 : Cmd T)
  | Cass(x : Var)(E : Expr)
  | Cread(x : Var)(E : Expr)
  | Cwrite(E1 E2 : Expr)
  | Cite(B : Cond)(C1 C2 : Cmd T)
  | Cwhile(B : Cond)(C : Cmd T)
  | Cpar(C1 C2 : Cmd T)
  | Calloc(x : Var)(E : Expr)
  | Cdispose(E : Expr)
  | Catomic(C : Cmd T)
  | Cinatom(C : Cmd T).

Add Search Blacklist "Cmd_rect".
Add Search Blacklist "Cmd_ind".
Add Search Blacklist "Cmd_rec".
Add Search Blacklist "Cmd_sind".

Arguments Cskip {_}.
Arguments Cseq {_}.
Arguments Cass {_}.
Arguments Cread {_}.
Arguments Cwrite {_}.
Arguments Cite {_}.
Arguments Cwhile {_}.
Arguments Cpar {_}.
Arguments Calloc {_}.
Arguments Cdispose {_}.
Arguments Catomic {_}.
Arguments Cinatom {_}.

(** A shorthand for doing induction over commands: *)

Ltac cmd_induction C :=
  induction C as [|
    (* sequential *)
    C1 IH1 C2 IH2|
    (* assignment *)
    x E|
    (* heap reading *)
    x E|
    (* heap writing *)
    E1 E2|
    (* if-then-else *)
    B C1 IH1 C2 IH2|
    (* while *)
    B C IH|
    (* parallel *)
    C1 IH1 C2 IH2|
    (* heap allocation *)
    x E|
    (* heap disposal *)
    E|
    (* atomics *)
    C IH|
    C IH
  ].

(** Some standard properties over the structure of commands. *)

Lemma cmd_neg_seq {T} :
  forall C2 C1 : Cmd T, ~ C2 = Cseq C1 C2.
Proof.
  cmd_induction C2; ins. intro. vauto.
  by apply IH2 in H.
Qed.

Lemma cmd_neg_ite_t {T} :
  forall (C1 C2 : Cmd T) B, ~ C1 = Cite B C1 C2.
Proof.
  cmd_induction C1; ins. intro. vauto.
  by apply IH1 in H1.
Qed.

Lemma cmd_neg_ite_f {T} :
  forall (C2 C1 : Cmd T) B, ~ C2 = Cite B C1 C2.
Proof.
  cmd_induction C2; ins. intro. vauto.
  by apply IH2 in H.
Qed.

(** **** Plain commands *)

(** Plain commands are commands without metadata components
    (or, technically, these are commands in which the metadata type is
    fixed and chosen to have only one inhabitant, namely [PMnone]). *)

Inductive PlainMetadata := PMnone.

Add Search Blacklist "PlainMetadata_rec".
Add Search Blacklist "PlainMetadata_ind".
Add Search Blacklist "PlainMetadata_rect".
Add Search Blacklist "PlainMetadata_sind".

Definition PlainCmd : Type := Cmd PlainMetadata.

Fixpoint plain {T} (C : Cmd T) : PlainCmd :=
  match C with
    | Cskip => Cskip
    | Cseq C1 C2 => Cseq (plain C1) (plain C2)
    | Cass x E => Cass x E
    | Cread x E => Cread x E
    | Cwrite E1 E2 => Cwrite E1 E2
    | Cite B C1 C2 => Cite B (plain C1) (plain C2)
    | Cwhile B C' => Cwhile B (plain C')
    | Cpar C1 C2 => Cpar (plain C1) (plain C2)
    | Calloc x E => Calloc x E
    | Cdispose E => Cdispose E
    | Catomic C' => Catomic (plain C')
    | Cinatom C' => Cinatom (plain C')
  end.

Lemma plain_skip {T} :
  forall C : Cmd T, plain C = Cskip -> C = Cskip.
Proof.
  cmd_induction C; intro H; intuition vauto.
Qed.

(** **** User programs *)

(** Any program is a _user program_ if it does not contain
    [Cinact] or [Cinatom] as a subprogram. *)

(** The program [Cinatom C] represents an atomic program [C]
    that is only partially executed. Such programs cannot be written
    by a user but are an artifact of the program dynamics.
    The same holds for [Cinact m C], which describes a partially
    executed action program [C] (and is a specification-only
    command besides). *)

Fixpoint cmd_user {T} (C : Cmd T) : Prop :=
  match C with
    | Cskip => True
    | Cseq C1 C2 => cmd_user C1 /\ cmd_user C2
    | Cass _ _ => True
    | Cread _ _ => True
    | Cwrite _ _ => True
    | Cite _ C1 C2 => cmd_user C1 /\ cmd_user C2
    | Cwhile _ C' => cmd_user C'
    | Cpar C1 C2 => cmd_user C1 /\ cmd_user C2
    | Calloc _ _ => True
    | Cdispose _ => True
    | Catomic C' => cmd_user C'
    | Cinatom _ => False
  end.

Lemma cmd_user_plain {T} :
  forall C : Cmd T, cmd_user C = cmd_user (plain C).
Proof.
  cmd_induction C; simpls;
    try (by rewrite IHC1, IHC2);
    by rewrite IH1, IH2.
Qed.

(** **** Locked programs *)

(** Any program is defined to be _locked_
    if it contains [Cinatom] as a subprogram. *)

Fixpoint cmd_locked {T} (C : Cmd T) : Prop :=
  match C with
    | Cseq C1 _ => cmd_locked C1
    | Cpar C1 C2 => cmd_locked C1 \/ cmd_locked C2
    | Cinatom _ => True
    | _ => False
  end.

Lemma cmd_locked_plain {T} :
  forall C : Cmd T, cmd_locked (plain C) = cmd_locked C.
Proof.
  cmd_induction C; ins. by rewrite IH1, IH2.
Qed.

(** **** Well-formed programs *)

(** Any program is defined to be _basic_ if it does not
    contain any process-related commands, and if there are
    no deadlocks in any of its parallel subprograms. *)

(** Any program is _well-formed_ if [C] is basic for every
    subcommand [Cact _ _ C] that occurs in the program, and if
    there are no deadlocks in any of its parallel subprograms,
    likewise to basic programs. *)

Fixpoint cmd_basic {T} (C : Cmd T) : Prop :=
  match C with
    | Cskip => True
    | Cseq C1 C2 => cmd_basic C1 /\ cmd_basic C2
    | Cass _ _ => True
    | Cread _ _ => True
    | Cwrite _ _ => True
    | Cite _ C1 C2 => cmd_basic C1 /\ cmd_basic C2
    | Cwhile _ C' => cmd_basic C'
    | Cpar C1 C2 => cmd_basic C1 /\ cmd_basic C2 /\ ~ (cmd_locked C1 /\ cmd_locked C2)
    | Calloc _ _ => True
    | Cdispose _ => True
    | Catomic C' => cmd_basic C'
    | Cinatom C' => cmd_basic C'
  end.

Fixpoint cmd_wf {T} (C : Cmd T) : Prop :=
  match C with
    | Cskip => True
    | Cseq C1 C2 => cmd_wf C1 /\ cmd_wf C2
    | Cass _ _ => True
    | Cread _ _ => True
    | Cwrite _ _ => True
    | Cite _ C1 C2 => cmd_wf C1 /\ cmd_wf C2
    | Cwhile _ C' => cmd_wf C'
    | Cpar C1 C2 => cmd_wf C1 /\ cmd_wf C2 /\ ~ (cmd_locked C1 /\ cmd_locked C2)
    | Calloc _ _ => True
    | Cdispose _ => True
    | Catomic C' => cmd_wf C'
    | Cinatom C' => cmd_wf C'
  end.

(** Any basic program is well-formed. *)

Lemma cmd_basic_wf {T} :
  forall C : Cmd T, cmd_basic C -> cmd_wf C.
Proof.
  cmd_induction C; intro H; simpls; intuition vauto.
Qed.

(** **** Free variables *)

(** The free variables of commands are defined in the standard way. *)

Fixpoint cmd_fv {T} (C : Cmd T)(x : Var) : Prop :=
  match C with
    | Cskip => False
    | Cass y E
    | Cread y E
    | Calloc y E => x = y \/ In x (expr_fv E)
    | Cwrite E1 E2 => In x (expr_fv E1) \/ In x (expr_fv E2)
    | Cite B C1 C2 => In x (cond_fv B) \/ cmd_fv C1 x \/ cmd_fv C2 x
    | Cwhile B C' => In x (cond_fv B) \/ cmd_fv C' x
    | Cseq C1 C2
    | Cpar C1 C2 => cmd_fv C1 x \/ cmd_fv C2 x
    | Cdispose E => In x (expr_fv E)
    | Catomic C'
    | Cinatom C' => cmd_fv C' x
  end.

Lemma cmd_fv_plain {T} :
  forall C : Cmd T, cmd_fv C = cmd_fv (plain C).
Proof.
  cmd_induction C; simpls; try (by rewrite IHC1, IHC2).
  - by rewrite IH1, IH2.
  - by rewrite IH1, IH2.
  - by rewrite IH.
  - by rewrite IH1, IH2.
Qed.

(** **** Modified variables *)

(** The operation [cmd_mod] captures the set of variables
    that are _modified_ (written to) by a given program,
    and is defined in the standard way (however, note that,
    for later convenience, [cmd_mod] is defined as a predicate,
    rather than a fixpoint operation that yields a list of variables). *)

Fixpoint cmd_mod {T} (C : Cmd T)(x : Var) : Prop :=
  match C with
    | Cskip => False
    | Cass y _
    | Cread y _ => x = y
    | Cwrite _ _ => False
    | Cseq C1 C2
    | Cpar C1 C2
    | Cite _ C1 C2 => cmd_mod C1 x \/ cmd_mod C2 x
    | Cwhile _ C' => cmd_mod C' x
    | Calloc y _ => x = y
    | Cdispose _ => False
    | Catomic C' => cmd_mod C' x
    | Cinatom C' => cmd_mod C' x
  end.

(** All variables written to by [C] occur freely in [C]. *)

Lemma cmd_fv_mod {T} :
  forall (C : Cmd T)(x : Var), cmd_mod C x -> cmd_fv C x.
Proof.
  cmd_induction C; intros y H; simpls; vauto.
  - destruct H as [H|H].
    left. by apply IH1.
    right. by apply IH2.
  - destruct H as [H|H].
    right. left. by apply IH1.
    right. right. by apply IH2.
  - right. by apply IH.
  - destruct H as [H|H].
    left. by apply IH1.
    right. by apply IH2.
  - by apply IH.
  - by apply IH.
Qed.

Lemma cmd_mod_plain {T} :
  forall C : Cmd T, cmd_mod C = cmd_mod (plain C).
Proof.
  cmd_induction C; simpls; by rewrite IH1, IH2.
Qed.


(** ** Dynamics *)

(** *** Stores *)

Definition Store := Var -> Val.

(** An update operation for stores: *)

Definition sUpdate (s : Store)(x : Var)(v : Val) : Store :=
  update var_eq_dec s x v.

Lemma sUpdate_comm :
  forall s x1 v1 x2 v2,
  x1 <> x2 ->
  sUpdate (sUpdate s x1 v1) x2 v2 =
  sUpdate (sUpdate s x2 v2) x1 v1.
Proof.
  intros s x1 v1 x2 v2 H1.
  extensionality y.
  unfold sUpdate, update. desf.
Qed.

(** The following definition captures two stores _agreeing_ on a
    given predicate [phi] over (program) variables. *)

Definition sAgree (phi : Var -> Prop)(s1 s2 : Store) : Prop :=
  forall x, phi x -> s1 x = s2 x.

(** Store agreement is a symmetric relation. *)

Global Instance sAgree_symm :
  forall phi, Symmetric (sAgree phi).
Proof.
  intros phi s1 s2 H1 x H2. symmetry. by apply H1.
Qed.

(** Below are several other useful properties of store agreement. *)

Lemma sAgree_split :
  forall phi1 phi2 s1 s2,
  sAgree (fun x => phi1 x \/ phi2 x) s1 s2 <->
  sAgree phi1 s1 s2 /\ sAgree phi2 s1 s2.
Proof.
  intros phi1 phi2 s1 s2. split; intro H1; [split|].
  - red. intros x H2. apply H1. by left.
  - red. intros x H2. apply H1. by right.
  - destruct H1 as (H1&H2). red. intros x [H3|H3].
    + by apply H1.
    + by apply H2.
Qed.

Lemma sAgree_app :
  forall xs1 xs2 s1 s2,
  sAgree (fun x => In x (xs1 ++ xs2)) s1 s2 <->
  sAgree (fun x => In x xs1) s1 s2 /\
  sAgree (fun x => In x xs2) s1 s2.
Proof.
  intros xs1 xs2 s1 s2. split; intro H1; [split|].
  - red. intros x H2. apply H1.
    apply in_or_app. by left.
  - red. intros x H2. apply H1.
    apply in_or_app. by right.
  - destruct H1 as (H1&H2). red. intros x H3.
    apply in_app_or in H3. destruct H3 as [H3|H3].
    + by apply H1.
    + by apply H2.
Qed.

Lemma sAgree_weaken :
  forall (phi1 phi2 : Var -> Prop)(s1 s2 : Store),
    (forall x, phi1 x -> phi2 x) ->
  sAgree phi2 s1 s2 ->
  sAgree phi1 s1 s2.
Proof.
  intros phi1 phi2 s1 s2 H1 H2 s H3.
  by apply H2, H1.
Qed.


(** *** Denotational semantics *)

(** **** Expressions *)

Fixpoint expr_eval (E : Expr)(s : Store) : Val :=
  match E with
    | Econst v => v
    | Evar x => s x
    | Eop E1 E2 => val_op (expr_eval E1 s) (expr_eval E2 s)
  end.

Definition expr_eval_map {T} (f : T -> Expr)(s : Store) : T -> Val :=
  fun x : T => expr_eval (f x) s.

(** Standard properties relating substitution to evaluation: *)

Lemma expr_eval_subst :
  forall E2 E1 x s,
  expr_eval (expr_subst x E1 E2) s =
  expr_eval E2 (sUpdate s x (expr_eval E1 s)).
Proof.
  expr_induction E2; intros E y s; simpls.
  - unfold sUpdate, update. desf.
  - by rewrite IH1, IH2.
Qed.

Lemma expr_eval_subst_map {T} :
  forall (f : T -> Expr) E x s,
  expr_eval_map (expr_subst_map x E f) s =
  expr_eval_map f (sUpdate s x (expr_eval E s)).
Proof.
  intros f E x s. extensionality y.
  apply expr_eval_subst.
Qed.

(** The evaluation of expressions only depends on its free variables. *)

Lemma expr_agree :
  forall E s1 s2,
  sAgree (fun x => In x (expr_fv E)) s1 s2 ->
  expr_eval E s1 = expr_eval E s2.
Proof.
  induction E as [v|x|E1 IH1 E2 IH2]; intros s1 s2 H; simpls.
  - apply H. vauto.
  - apply sAgree_app in H. destruct H as (H1&H2).
    by rewrite IH1 with s1 s2, IH2 with s1 s2.
Qed.

Lemma expr_map_agree {T} :
  forall (f : T -> Expr) s1 s2,
    (forall x, expr_map_fv f x -> s1 x = s2 x) ->
  expr_eval_map f s1 = expr_eval_map f s2.
Proof.
  intros f s1 s2 H1.
  extensionality t. apply expr_agree.
  red. intros x H2. apply H1.
  by exists t.
Qed.

(** The following lemma relates expression evaluation to store updates. *)

Lemma expr_eval_upd :
  forall E s x v,
  ~ In x (expr_fv E) ->
  expr_eval E (sUpdate s x v) = expr_eval E s.
Proof.
  intros E s x v H1.
  rewrite expr_agree with E s (sUpdate s x v); vauto.
  intros y H2. unfold sUpdate, update. desf.
Qed.

(** Other useful properties of expression evaluation. *)

Lemma expr_eval_const :
  forall E s, expr_eval E s = expr_eval (Econst (expr_eval E s)) s.
Proof. expr_induction E; intro s; vauto. Qed.


(** **** Conditions *)

Fixpoint cond_eval (B : Cond)(s : Store) : bool :=
  match B with
    | Bconst b => b
    | Bnot B' => negb (cond_eval B' s)
    | Band B1 B2 => (cond_eval B1 s) && (cond_eval B2 s)
    | Beq E1 E2 => if val_eq_dec (expr_eval E1 s) (expr_eval E2 s) then true else false
  end.

Lemma cond_eval_excl :
  forall B s, cond_eval B s = true \/ cond_eval B s = false.
Proof.
  intros B s. rewrite <- Bool.not_true_iff_false.
  apply classic.
Qed.

(** A standard property that relates substitution to evaluation: *)

Lemma cond_eval_subst :
  forall B E x s,
  cond_eval (cond_subst x E B) s =
  cond_eval B (sUpdate s x (expr_eval E s)).
Proof.
  induction B as [b|B' IH|B1 IH1 B2 IH2|E1 E2];
    intros E x s; simpl; intuition.
  - by rewrite IH.
  - by rewrite IH1, IH2.
  - by repeat rewrite expr_eval_subst.
Qed.

(** The evaluation of conditions only depends on its free variables. *)

Lemma cond_agree :
  forall B s1 s2,
  sAgree (fun x => In x (cond_fv B)) s1 s2 ->
  cond_eval B s1 = cond_eval B s2.
Proof.
  induction B as [b|B' IH|B1 IH1 B2 IH2|E1 E2];
    intros s1 s2 H; simpls.
  - by rewrite IH with s1 s2.
  - apply sAgree_app in H. destruct H as (H1&H2).
    by rewrite IH1 with s1 s2, IH2 with s1 s2.
  - apply sAgree_app in H. destruct H as (H1&H2).
    by rewrite expr_agree with E1 s1 s2, expr_agree with E2 s1 s2.
Qed.

(** The following lemma relates condition evaluation to store updates. *)

Lemma cond_eval_upd :
  forall B s x v,
  ~ In x (cond_fv B) ->
  cond_eval B (sUpdate s x v) = cond_eval B s.
Proof.
  intros B s x v H1.
  rewrite cond_agree with B s (sUpdate s x v); vauto.
  intros y H2. unfold sUpdate, update. desf.
Qed.

(** *** Shared memory accesses *)

(** The operation [cmd_acc C s] defines the set of heap locations
    that are _accessed_ by the program [C] in a single execution step,
    where [s] is used to evaluate all expressions referring
    to heap locations. *)

(** Likewise, the operation [cmd_writes C s] determines the set
    of heap locations that are _written to_ by [C]
    in a single execution step. Note that, rather than yielding
    a set of heap locations, both these operations are defined
    as predicates instead for later convenience. *)

Fixpoint cmd_acc {T} (C : Cmd T)(s : Store)(l : Val) : Prop :=
  match C with
    | Cskip => False
    | Cseq C' _ => cmd_acc C' s l
    | Cass _ _ => False
    | Cread _ E
    | Cwrite E _ => l = expr_eval E s
    | Cite _ _ _
    | Cwhile _ _ => False
    | Cpar C1 C2 => cmd_acc C1 s l \/ cmd_acc C2 s l
    | Calloc _ _ => False
    | Cdispose E => l = expr_eval E s
    | Catomic _ => False
    | Cinatom C' => cmd_acc C' s l
  end.

Fixpoint cmd_writes {T} (C : Cmd T)(s : Store)(l : Val) : Prop :=
  match C with
    | Cskip => False
    | Cseq C' _ => cmd_writes C' s l
    | Cass _ _
    | Cread _ _ => False
    | Cwrite E _ => l = expr_eval E s
    | Cite _ _ _
    | Cwhile _ _ => False
    | Cpar C1 C2 => cmd_writes C1 s l \/ cmd_writes C2 s l
    | Calloc _ _ => False
    | Cdispose E => l = expr_eval E s
    | Catomic _ => False
    | Cinatom C' => cmd_writes C' s l
  end.

(** All writes to shared memory are also shared-memory accesses. *)

Lemma cmd_writes_acc {T} :
  forall (C : Cmd T) s l, cmd_writes C s l -> cmd_acc C s l.
Proof.
  cmd_induction C; intros s l H; simpls; vauto.
  - by apply IH1.
  - destruct H as [H|H].
    + left. by apply IH1.
    + right. by apply IH2.
  - by apply IH.
Qed.

(** Other useful properties of shared-memory accesses. *)

Lemma cmd_acc_agree {T} :
  forall (C : Cmd T) s1 s2 l,
  sAgree (cmd_fv C) s1 s2 ->
  cmd_acc C s1 l = cmd_acc C s2 l.
Proof.
  cmd_induction C; intros s1 s2 l H; simpls; vauto.
  - apply sAgree_split in H.
    destruct H as (H1&H2).
    rewrite IH1 with (s2:=s2); auto.
  - apply sAgree_split in H.
    destruct H as (H1&H2).
    rewrite expr_agree with (s2:=s2); auto.
  - apply sAgree_split in H.
    destruct H as (H1&H2).
    rewrite expr_agree with (s2:=s2); auto.
  - apply sAgree_split in H.
    destruct H as (H1&H2).
    rewrite IH1 with (s2:=s2), IH2 with (s2:=s2); auto.
  - rewrite expr_agree with (s2:=s2); auto.
  - rewrite IH with (s2:=s2); auto.
Qed.

Lemma cmd_writes_agree {T} :
  forall (C : Cmd T) s1 s2 l,
    (forall x, cmd_fv C x -> s1 x = s2 x) ->
  cmd_writes C s1 l = cmd_writes C s2 l.
Proof.
  cmd_induction C; intros s1 s2 l H; simpls; vauto.
  - rewrite IH1 with (s2:=s2); auto.
  - rewrite expr_agree with (s2:=s2); auto.
    red. ins. apply H. by left.
  - rewrite IH1 with (s2:=s2), IH2 with (s2:=s2); auto.
  - rewrite expr_agree with (s2:=s2); auto.
  - rewrite IH with (s2:=s2); auto.
Qed.

Lemma cmd_acc_plain {T} :
  forall (C : Cmd T) s, cmd_acc (plain C) s = cmd_acc C s.
Proof.
  cmd_induction C; intros s; simpls; vauto.
  by rewrite IH1, IH2.
Qed.

Lemma cmd_writes_plain {T} :
  forall (C : Cmd T) s,
  cmd_writes (plain C) s = cmd_writes C s.
Proof.
  cmd_induction C; intros s; simpls; vauto.
  by rewrite IH1, IH2.
Qed.


(** *** Operational semantics *)

(** Below are the small-step reduction rules of the (standard)
    operational semantics of programs. *)

(** Observe that the process-related commands are ignored
    and handled as if they were comments, since these are
    specification-only. Moreover, the transition rules for the
    parallel composition only allow a program to make a step if the
    other program is not locked. This allows to model atomic programs
    using a small-step semantics. *)

Inductive step : Heap -> Store -> PlainCmd -> Heap -> Store -> PlainCmd -> Prop :=
  (* sequential *)
  | step_seq_l h s C1 h' s' C1' C2 :
    step h s C1 h' s' C1' ->
    step h s (Cseq C1 C2) h' s' (Cseq C1' C2)
  | step_seq_r h s C :
    step h s (Cseq Cskip C) h s C
  (* assign *)
  | step_assign h s x E :
    let v := expr_eval E s in
    step h s (Cass x E) h (sUpdate s x v) Cskip
  (* heap reading *)
  | step_read h s x E v :
    h (expr_eval E s) = Some v ->
    step h s (Cread x E) h (sUpdate s x v) Cskip
  (* heap writing *)
  | step_write h s E1 E2 v :
    let l := expr_eval E1 s in
    let v' := expr_eval E2 s in
    h l = Some v ->
    step h s (Cwrite E1 E2) (hUpdate h l (Some v')) s Cskip
  (* if-then-else *)
  | step_ite_t h s B C1 C2 :
    cond_eval B s = true ->
    step h s (Cite B C1 C2) h s C1
  | step_ite_f h s B C1 C2 :
    cond_eval B s = false ->
    step h s (Cite B C1 C2) h s C2
  (* while *)
  | step_while h s B C :
    step h s (Cwhile B C) h s (Cite B (Cseq C (Cwhile B C)) Cskip)
  (* heap (de)alloc *)
  | step_alloc h s x E l :
    let v := expr_eval E s in
    h l = None ->
    step h s (Calloc x E) (hUpdate h l (Some v)) (sUpdate s x l) Cskip
  | step_dispose h s E :
    let l := expr_eval E s in
    step h s (Cdispose E) (hUpdate h l None) s Cskip
  (* atomics *)
  | step_atom h s C :
    step h s (Catomic C) h s (Cinatom C)
  | step_inatom_l h s C h' s' C' :
    step h s C h' s' C' ->
    step h s (Cinatom C) h' s' (Cinatom C')
  | step_inatom_r h s :
    step h s (Cinatom Cskip) h s Cskip
  (* parallel *)
  | step_par_l h s C1 C2 h' s' C1' :
    step h s C1 h' s' C1' ->
    ~ cmd_locked C2 ->
    step h s (Cpar C1 C2) h' s' (Cpar C1' C2)
  | step_par_r h s C1 C2 h' s' C2' :
    step h s C2 h' s' C2' ->
    ~ cmd_locked C1 ->
    step h s (Cpar C1 C2) h' s' (Cpar C1 C2')
  | step_par_done h s :
    step h s (Cpar Cskip Cskip) h s Cskip.

Add Search Blacklist "step_ind".
Add Search Blacklist "step_sind".

(** Program basicality, program well-formedness
    and heap finiteness all remain invariant
    during program execution. *)

Lemma step_basic_pres :
  forall C h s C' h' s',
  cmd_basic C -> step h s C h' s' C' -> cmd_basic C'.
Proof.
  cmd_induction C; intros h s C'' h' s' H1 H2;
    inv H2; simpls; desf; intuition vauto.
  - by apply IH1 in H8.
  - by apply IH1 in H5.
  - by apply IH2 in H5.
  - by apply IH in H4.
Qed.

Lemma step_wf_pres :
  forall C h s C' h' s',
  cmd_wf C -> step h s C h' s' C' -> cmd_wf C'.
Proof.
  cmd_induction C; intros h s C'' h' s' H1 H2;
    inv H2; simpls; desf; intuition vauto.
  - by apply IH1 in H8.
  - by apply IH1 in H5.
  - by apply IH2 in H5.
  - by apply IH in H4.
Qed.

Lemma step_hFinite :
  forall C h s C' h' s',
  step h s C h' s' C' -> hFinite h -> hFinite h'.
Proof.
  cmd_induction C; intros h s C'' h' s' STEP FIN; inv STEP; vauto.
  - by apply IH1 in H6.
  - by apply hFinite_update.
  - by apply IH1 in H3.
  - by apply IH2 in H3.
  - by apply hFinite_update.
  - by apply hFinite_update.
  - by apply IH in H2.
Qed.

(** The sets of free and modified variables do not grow
    during program execution. *)

Lemma step_fv_mod :
  forall C h s C' h' s',
  step h s C h' s' C' ->
    (forall x, cmd_fv C' x -> cmd_fv C x) /\
    (forall x, cmd_mod C' x -> cmd_mod C x) /\
    (forall x, ~ cmd_mod C x -> s x = s' x).
Proof.
  cmd_induction C; intros h s C'' h' s' H1; inv H1; clear H1; simpls.
  (* sequential *)
  - repeat split; intros x H.
    + destruct H as [H|H]; vauto.
      apply IH1 in H7. destruct H7 as (H1&H2&H3).
      left. by apply H1.
    + destruct H as [H|H]; vauto.
      apply IH1 in H7. destruct H7 as (H1&H2&H3).
      left. by apply H2.
    + apply IH1 in H7. destruct H7 as (H1&H2&H3).
      apply H3. intro H4. apply H. by left.
  - repeat split; intros x H; by right.
  (* assign *)
  - repeat split; intros y H; vauto.
    unfold sUpdate, update. intuition desf.
  (* heap reading *)
  - repeat split; intros y H; vauto.
    unfold sUpdate, update. intuition desf.
  (* if-then-else *)
  - repeat split; intros y H; vauto.
  - repeat split; intros y H; vauto.
  (* while *)
  - repeat split; intros y H; vauto.
    destruct H as [|[|]]; vauto.
    destruct H as [|[|]]; vauto.
    destruct H as [[|]|]; vauto.
  (* parallel *)
  - apply IH1 in H4. clear IH1 IH2.
    destruct H4 as (H1&H2&H3).
    repeat split; intros y H; vauto.
    destruct H as [H|H].
    left. by apply H1. by right.
    destruct H as [H|H].
    left. by apply H2. by right.
    apply H3. intro H4. apply H. by left.
  - apply IH2 in H4. clear IH1 IH2.
    destruct H4 as (H1&H2&H3).
    repeat split; intros y H; vauto.
    destruct H as [H|H].
    by left. right. by apply H1.
    destruct H as [H|H].
    by left. right. by apply H2.
    apply H3. intro H4. apply H. by right.
  (* heap allocation *)
  - repeat split; intros y H; vauto.
    unfold sUpdate, update. intuition desf.
  (* atomics *)
  - apply IH in H3. desf.
Qed.

(** Program execution commutes with store agreement: *)

Lemma step_agree :
  forall C h s1 s2 C' h' s1' (phi : Var -> Prop),
    (forall x, cmd_fv C x -> phi x) ->
    (sAgree phi s1 s2) ->
    step h s1 C h' s1' C' ->
  exists s2',
    (sAgree phi s1' s2') /\
    step h s2 C h' s2' C'.
Proof.
  cmd_induction C; intros h s1 s2 C'' h' s1' phi H1 H2 STEP;
    inv STEP; clear STEP; simpls; intuition vauto;
    unfold sAgree in *; try (exists s2; intuition vauto; fail).
  (* sequential *)
  - apply IH1 with (s2:=s2)(phi:=phi) in H8; vauto.
    destruct H8 as (s2'&H3&STEP).
    exists s2'. intuition vauto.
    intros x H. apply H1. by left.
  (* assignment *)
  - exists (sUpdate s2 x (expr_eval E s2)).
    split; vauto. intros y H. unfold sUpdate, update.
    destruct (var_eq_dec x y); auto. clarify.
    rewrite <- expr_agree with (s1:=s1); auto.
    unfold sAgree. intros x H'.
    apply H2, H1. by right.
  (* heap reading *)
  - rewrite expr_agree with (s2:=s2) in H8; vauto.
    exists (sUpdate s2 x v). split; vauto.
    intros y H3. unfold sUpdate, update.
    destruct (var_eq_dec x y); auto.
    red. intros y H. apply H2, H1. by right.
  (* heap writing *)
  - subst l l0 v' v'0.
    exists s2. split; vauto.
    rewrite expr_agree with (s2:=s2) in H8; vauto.
    repeat rewrite expr_agree with (s1:=s1')(s2:=s2); vauto.
    red. ins. apply H2, H1. by right.
    red. ins. apply H2, H1. by left.
    red. ins. apply H2, H1. by left.
  (* if-then-else *)
  - exists s2. split; vauto. constructor.
    rewrite <- cond_agree with (s1:=s1'); auto.
    red. ins. apply H2, H1. by left.
  - exists s2. split; vauto. constructor.
    rewrite <- cond_agree with (s1:=s1'); auto.
    red. ins. apply H2, H1. by left.
  (* parallel *)
  - apply IH1 with (s2:=s2)(phi:=phi) in H5; vauto.
    destruct H5 as (s2'&H3&H4).
    exists s2'. split; vauto.
    intros x H. apply H1. by left.
  - apply IH2 with (s2:=s2)(phi:=phi) in H5; vauto.
    destruct H5 as (s2'&H3&H4).
    exists s2'. split; vauto.
    intros x H. apply H1. by right.
  (* heap (de)allocation *)
  - subst v. rewrite expr_agree with (s2:=s2).
    exists (sUpdate s2 x l).
    split; vauto. intros y H3.
    unfold sUpdate, update.
    destruct (var_eq_dec x y); auto.
    red. ins. apply H2, H1. by right.
  - subst l l0. exists s2. split; vauto.
    rewrite expr_agree with (s2:=s2); vauto.
    red. ins. by apply H2, H1.
  (* atomics *)
  - apply IH with (s2:=s2)(phi:=phi) in H4; vauto.
    destruct H4 as (s2'&H4&H5).
    exists s2'. intuition vauto.
Qed.

(** A program reduction step always mutates the executed program;
    one does not end up in the same program after performing a
    computation step. *)

Lemma step_neg_C :
  forall C h s h' s', ~ step h s C h' s' C.
Proof.
  cmd_induction C; intros h s h' s' STEP;
    vauto; inv STEP; clear STEP.
  (* sequential *)
  - by apply IH1 in H5.
  - by apply cmd_neg_seq in H5.
  (* if-then-else *)
  - by apply cmd_neg_ite_t in H6.
  - by apply cmd_neg_ite_f in H6.
  (* parallel *)
  - by apply IH1 in H6.
  - by apply IH2 in H6.
  (* atomics *)
  - by apply IH in H5.
Qed.


(** *** Fault semantics *)

(** The fault semantics of program is defined in
    terms of the predicate [fault h s C] and captures
    whether [C] is able to _fault_ in a single computation
    step with respect to heap [h] and store [s]. *)

(** A _fault_ is defined to be a data-race, a deadlock,
    or a violation of memory safety. *)

(** Any program performs a _data-race_ if two threads
    access the same shared location,
    where one of these accesses is a write. *)

(** Any parallel program [Cpar C1 C2] is _deadlocked_ if
    [C1] and [C2] are both locked with respect to [cmd_locked]. *)

(** Moreover, any program is defined to be _memory safe_
    if it does not access a shared location has has not
    been allocated. *)

Inductive fault {T} : Heap -> Store -> Cmd T -> Prop :=
  (* heap reading *)
  | fault_read h s x E :
    h (expr_eval E s) = None -> fault h s (Cread x E)
  (* heap writing *)
  | fault_write h s E1 E2 :
    h (expr_eval E1 s) = None -> fault h s (Cwrite E1 E2)
  (* heap (de)allocation *)
  | fault_alloc h s x E :
    (~ exists l, h l = None) -> fault h s (Calloc x E)
  | fault_dispose h s E :
    h (expr_eval E s) = None -> fault h s (Cdispose E)
  (* parallel *)
  | fault_par_l h s C1 C2 :
    fault h s C1 -> ~ cmd_locked C2 -> fault h s (Cpar C1 C2)
  | fault_par_r h s C1 C2 :
    fault h s C2 -> ~ cmd_locked C1 -> fault h s (Cpar C1 C2)
  | fault_deadlock h s C1 C2 :
    cmd_locked C1 -> cmd_locked C2 -> fault h s (Cpar C1 C2)
  (* sequential *)
  | fault_seq h s C1 C2 :
    fault h s C1 -> fault h s (Cseq C1 C2)
  (* atomics *)
  | fault_atom h s C :
    fault h s C -> fault h s (Cinatom C)
  (* data races *)
  | fault_race_l h s C1 C2 :
    ~ cmd_locked C1 ->
    ~ cmd_locked C2 ->
    ~ disjoint (cmd_writes C1 s) (cmd_acc C2 s) ->
    fault h s (Cpar C1 C2)
  | fault_race_r h s C1 C2 :
    ~ cmd_locked C1 ->
    ~ cmd_locked C2 ->
    ~ disjoint (cmd_acc C1 s) (cmd_writes C2 s) ->
    fault h s (Cpar C1 C2).

Add Search Blacklist "fault_ind".
Add Search Blacklist "fault_sind".

(** The fault semantics of programs is closed under store agreement. *)

Lemma fault_agree {T} :
  forall (C : Cmd T) h s1 s2,
  sAgree (cmd_fv C) s1 s2 -> fault h s1 C -> fault h s2 C.
Proof.
  cmd_induction C; intros h s1 s2 H1 H2;
    simpls; inv H2; clear H2.
  (* sequential *)
  - constructor. apply IH1 with s1; vauto.
    red. ins. apply H1. by left.
  (* heap reading *)
  - constructor.
    rewrite <- expr_agree with (s1 := s1); auto.
    unfold sAgree. intros y H2.
    apply H1. by right.
  (* heap writing *)
  - constructor.
    rewrite <- expr_agree with (s1 := s1); auto.
    unfold sAgree. intros y H2.
    apply H1. by left.
  (* parallel *)
  - apply fault_par_l; vauto.
    apply IH1 with s1; auto.
    red. ins. apply H1. vauto.
  - apply fault_par_r; vauto.
    apply IH2 with s1; auto.
    red. ins. apply H1. vauto.
  - by apply fault_deadlock.
  (* data races *)
  - apply sAgree_split in H1.
    destruct H1 as (H1&H2).
    apply fault_race_l; vauto.
    intro H4. apply H7. clear H7.
    red. intros l F1 F2.
    rewrite cmd_writes_agree with (s4:=s2) in F1; auto.
    rewrite cmd_acc_agree with (s4:=s2) in F2; auto.
    by apply H4 with l.
  - apply sAgree_split in H1.
    destruct H1 as (H1&H2).
    apply fault_race_r; vauto.
    intro H4. apply H7. clear H7.
    red. intros l F1 F2.
    rewrite cmd_acc_agree with (s4:=s2) in F1; auto.
    rewrite cmd_writes_agree with (s4:=s2) in F2; auto.
    by apply H4 with l.
  (* heap (de)allocation *)
  - by constructor.
  - constructor. rewrite <- expr_agree with (s1:=s1); auto.
  (* atomics *)
  - constructor. apply IH with s1; auto.
Qed.

(** The following theorem shows that the operational semantics
    and fault semantics are coherent, by showing a property
    of progress: every configuration that does not fault
    can either make a computation step or has already terminated. *)

Theorem step_progress :
  forall C h s,
  ~ fault h s C -> C = Cskip \/ exists C' h' s', step h s C h' s' C'.
Proof.
  cmd_induction C; intros h s FAULT.
  (* skip *)
  - by left.
  (* sequential *)
  - assert (H1 : C1 = Cskip \/ ~ C1 = Cskip) by apply classic.
    right. destruct H1 as [H1|H1].
    (* left program [C1] is empty *)
    + clarify. exists C2, h, s. vauto.
    (* left program [C1] is not empty *)
    + assert (H2 : ~ fault h s C1) by (intro H; apply FAULT; vauto).
      apply IH1 in H2. destruct H2 as [H2|H2]; vauto.
      destruct H2 as (C1'&h'&s'&STEP).
      exists (Cseq C1' C2), h', s'. vauto.
  (* assignment *)
  - right. exists Cskip, h, (sUpdate s x (expr_eval E s)).
    constructor.
  (* heap reading *)
  - right. cut (exists v, h (expr_eval E s) = Some v).
    + intro H1. destruct H1 as (v&H1).
      exists Cskip, h, (sUpdate s x v). vauto.
    + rewrite <- option_not_none.
      intro H1. apply FAULT. vauto.
  (* heap writing *)
  - right. cut (exists v, h (expr_eval E1 s) = Some v).
    + intro H1. destruct H1 as (v&H1).
      exists Cskip, (hUpdate h (expr_eval E1 s) (Some (expr_eval E2 s))), s.
      by apply step_write with v.
    + rewrite <- option_not_none.
      intro H. apply FAULT. vauto.
  (* if-then-else *)
  - assert (H1 : cond_eval B s = true \/ cond_eval B s = false)
      by apply cond_eval_excl.
    right. destruct H1 as [H1|H1].
    + exists C1, h, s. vauto.
    + exists C2, h, s. vauto.
  (* while *)
  - right. exists (Cite B (Cseq C (Cwhile B C)) Cskip), h, s. vauto.
  (* parallel composition *)
  - right.
    cut ((~ cmd_locked C2 /\ exists C1' h' s', step h s C1 h' s' C1') \/
         (~ cmd_locked C1 /\ exists C2' h' s', step h s C2 h' s' C2') \/
          C1 = Cskip /\ C2 = Cskip).
    (* progress for all three cases in the cut *)
    + intro H. destruct H as [H|[H|H]].
      (* [C1] makes a step *)
      * destruct H as (H&C1'&h'&s'&STEP).
        exists (Cpar C1' C2), h', s'. vauto.
      (* [C2] makes a step *)
      * destruct H as (H&C2'&h'&s'&STEP).
        exists (Cpar C1 C2'), h', s'. vauto.
      (* [C1] and [C2] have both terminated *)
      * destruct H as (H1&H2). clarify.
        exists Cskip, h, s. vauto.
    (* one of the three cases in the cut must hold *)
    + assert (H1 : C1 = Cskip \/ ~ C1 = Cskip) by apply classic.
      assert (H2 : C2 = Cskip \/ ~ C2 = Cskip) by apply classic.
      desf.
      (* [C1] and [C2] have both terminated *)
      * by repeat right.
      (* [C2] has terminated, [C1] has not *)
      * left. split. intro H3. inv H3.
        apply imply_and_or with (C1 = Cskip); vauto.
        apply IH1. intro FAULT'.
        apply FAULT. vauto.
      (* [C1] has terminated, [C2] has not *)
      * right. left. split.
        ** intro H3. inv H3.
        ** apply imply_and_or with (C2 = Cskip); vauto.
           apply IH2. intro FAULT'.
           apply FAULT. vauto.
      (* [C1] and [C2] have both not terminated *)
      * assert (H3 : cmd_locked C1 \/ ~ cmd_locked C1) by apply classic.
        destruct H3 as [H3|H3].
        (* [C1] is locked *)
        ** assert (H : ~ cmd_locked C2). {
            intro H4. apply FAULT. vauto. }
           left. split. auto.
           apply imply_and_or with (C1 = Cskip); vauto.
           apply IH1. intro FAULT'.
           apply FAULT. vauto.
        (* [C1] is not locked *)
        ** right. left. split. auto.
           apply imply_and_or with (C2 = Cskip); vauto.
           apply IH2. intro FAULT'.
           apply FAULT. vauto.
  (* heap (de)allocation *)
  - right. cut (exists l, h l = None).
    + intro H. destruct H as (l&H).
      exists Cskip, (hUpdate h l (Some (expr_eval E s))), (sUpdate s x l). vauto.
    + apply NNPP. intro H. apply FAULT. vauto.
  - right. exists Cskip,
      (hUpdate h (expr_eval E s) None), s. vauto.
  (* atomics *)
  - right. exists (Cinatom C), h, s. vauto.
  - assert (H : C = Cskip \/ ~ C = Cskip) by apply classic.
    destruct H as [H|H].
    (* [C] has terminated *)
    + clarify. right. exists Cskip, h, s. vauto.
    (* [C] has not terminated *)
    + cut (~ fault h s C).
      * intro H1. apply IH in H1.
        destruct H1 as [H1|H1]; vauto.
        destruct H1 as (C'&h'&s'&STEP).
        right. exists (Cinatom C'), h', s'. vauto.
      * intro H1. apply FAULT. vauto.
Qed.


End Programs.
