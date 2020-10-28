Require Import HahnBase.
Require Import List.
Require Import Permissions.
Require Import PermSolver.
Require Import Permutation.
Require Import PermutationTactic.
Require Import Prelude.
Require Import QArith.
Require Import Qcanon.
Require Import Setoid.
Require Import Utf8.

Import ListNotations.

Set Implicit Arguments.


(** * Heaps *)

Module Type Heaps(dom : Domains).
  Export dom.


(** ** Ordinary heaps *)

Definition Heap := Val -> option Val.

(** The _identity heap_ is empty at every location: *)

Definition hIden : Heap := fun _ => None.

(** Update operation for heaps: *)

Definition hUpdate (h : Heap)(l : Val)(v : option Val) :=
  update val_eq_dec h l v.


(** *** Finiteness *)

(** A heap is _finite_ if all mappings that are not free
    can be mapped to some finite structure, in this case a list. *)

Definition hFinite (h : Heap) : Prop :=
  exists xs : list Val, forall l, h l <> None -> In l xs.

Lemma hFinite_iden : hFinite hIden.
Proof. red. exists nil. intros l H. vauto. Qed.

(** The most important property of finite heaps is that
    one can always find a free entry, as shown below. *)

Lemma hFinite_free :
  forall h, hFinite h -> exists l, h l = None.
Proof.
  intros h (xs&FIN).
  assert (H1 : exists l, ~ In l xs) by apply val_inf.
  destruct H1 as (l&H).
  specialize FIN with l.
  exists l. tauto.
Qed.

(** Any heap update preserves finiteness. *)

Lemma hFinite_update :
  forall h l v,
  hFinite h -> hFinite (hUpdate h l v).
Proof.
  intros p l val (xs&FIN).
  assert (H1 : val = None \/ ~ val = None) by apply classic.
  destruct H1 as [H1|H1].
  (* [val] is free *)
  - exists xs. intros l' H2. apply FIN.
    unfold hUpdate, update in H2. desf.
  (* [val] is not free *)
  - exists (l :: xs).
    intros l' H2. specialize FIN with l'. simpls.
    unfold hUpdate, update in H2.
    destruct (val_eq_dec l l') as [|H3]; vauto.
    right. by apply FIN.
Qed.


(** ** Permission heaps cells *)

(** The set [PermHeapCell] of _permission heap cells_
    is later used as the codomain of permission heaps. *)

(** Permission heap cells can be free, invalid or occupied.
    There are three kinds of occupied heap cells, which correspond
    to the three different heap ownership predicates in the logic. *)

(** Notice that _action heap cells_ hold an extra value,
    which is a copy of the value at that heap location,
    made at the moment the action heap cell was created. *)

Inductive PermHeapCell :=
  | PHCfree
  | PHCstd(q : Qc)(v : Val)
  | PHCinvalid.

Add Search Blacklist "PermHeapCell_rect".
Add Search Blacklist "PermHeapCell_ind".
Add Search Blacklist "PermHeapCell_rec".
Add Search Blacklist "PermHeapCell_sind".


Inductive GuardHeapCell :=
  | GHCfree
  | GHCstd(q : Qc)
  | GHCinvalid.

(** *** Validity *)

(** Any permission heap cell [phc] is _valid_ if [phc]
    is not (explicitly) invalid, and any underlying
    fractional permission is valid. *)

Definition phcValid (phc : PermHeapCell) : Prop :=
  match phc with
    | PHCfree => True
    | PHCstd q _ => perm_valid q
    | PHCinvalid => False
  end.

Notation "√ phc" :=
  (phcValid phc)
  (only printing, at level 80).

Definition ghcValid (ghc : GuardHeapCell) : Prop :=
  match ghc with
    | GHCfree => True
    | GHCstd q => perm_valid q
    | GHCinvalid => False
  end.

Notation "√ ghc" :=
  (ghcValid ghc)
  (only printing, at level 80).

(** Free cells are always valid, whereas invalid cells are never valid. *)

Lemma phcValid_free : phcValid PHCfree.
Proof. ins. Qed.

Lemma phcValid_contra :
  forall phc, phcValid phc -> phc <> PHCinvalid.
Proof.
  intros phc H. unfold phcValid in H. desf.
Qed.

Hint Resolve phcValid_free phcValid_contra : core.

Lemma ghcValid_free : ghcValid GHCfree.
Proof. ins. Qed.

Lemma ghcValid_contra :
  forall ghc, ghcValid ghc -> ghc <> GHCinvalid.
Proof.
  intros ghc H. unfold ghcValid in H. desf.
Qed.

Hint Resolve ghcValid_free ghcValid_contra : core.


(** *** Disjointness *)

(** Any two permission heap cells are said to be _disjoint_
    if their underlying fractional permissions are disjoint,
    an all other components are equal apart from that. *)

(** Invalid heap cells are never disjoint with any other heap cell,
    while free heap cells are disjoint with other valid heap cells. *)

Definition phcDisj (phc1 phc2 : PermHeapCell) : Prop :=
  match phc1, phc2 with
    | PHCinvalid, _
    | _, PHCinvalid => False
    | PHCfree, PHCfree => True
    | PHCfree, phc
    | phc, PHCfree => phcValid phc
    | PHCstd q1 v1, PHCstd q2 v2 =>
        perm_disj q1 q2 /\ v1 = v2
  end.

Notation "phc1 ⟂ phc2" :=
  (phcDisj phc1 phc2)
  (only printing, at level 80).


Definition ghcDisj (ghc1 ghc2 : GuardHeapCell) : Prop :=
  match ghc1, ghc2 with
    | GHCinvalid, _
    | _, GHCinvalid => False
    | GHCfree, GHCfree => True
    | GHCfree, ghc
    | ghc, GHCfree => ghcValid ghc
    | GHCstd q1, GHCstd q2 =>
        perm_disj q1 q2
  end.

Notation "ghc1 ⟂ ghc2" :=
  (ghcDisj ghc1 ghc2)
  (only printing, at level 80).

(** Heap cell disjointness is a symmetric relation *)

Global Instance phcDisj_symm : Symmetric phcDisj.
Proof.
  unfold phcDisj. red.
  ins; desf; simpls; intuition.
Qed.

Global Instance ghcDisj_symm : Symmetric ghcDisj.
Proof.
  unfold ghcDisj. red.
  ins; desf; simpls; intuition.
Qed.

(** Below are the identity laws for disjointness: *)

Lemma phcDisj_free_l :
  forall phc, phcValid phc -> phcDisj phc PHCfree.
Proof. ins. red. desf. Qed.
Lemma phcDisj_free_r :
  forall phc, phcValid phc -> phcDisj PHCfree phc.
Proof. ins. desf. Qed.

Hint Resolve phcDisj_free_l phcDisj_free_r : core.


Lemma ghcDisj_free_l :
  forall ghc, ghcValid ghc -> ghcDisj ghc GHCfree.
Proof. ins. red. desf. Qed.
Lemma ghcDisj_free_r :
  forall ghc, ghcValid ghc -> ghcDisj GHCfree ghc.
Proof. ins. desf. Qed.

Hint Resolve ghcDisj_free_l ghcDisj_free_r : core.

(** Below are some other useful properties of disjointness. *)

Lemma phcDisj_valid_l :
  forall phc1 phc2, phcDisj phc1 phc2 -> phcValid phc1.
Proof.
  unfold phcDisj, phcValid.
  intros ?? H.
  repeat desf; try (by apply perm_disj_valid in H; desf).
Qed.
Lemma phcDisj_valid_r :
  forall phc1 phc2, phcDisj phc1 phc2 -> phcValid phc2.
Proof.
  intros ?? H. symmetry in H.
  by apply phcDisj_valid_l in H.
Qed.
Lemma phcDisj_valid :
  forall phc1 phc2,
  phcDisj phc1 phc2 -> phcValid phc1 /\ phcValid phc2.
Proof.
  intros phc1 phc2 H. split.
  - by apply phcDisj_valid_l in H.
  - by apply phcDisj_valid_r in H.
Qed.


Lemma ghcDisj_valid_l :
  forall ghc1 ghc2, ghcDisj ghc1 ghc2 -> ghcValid ghc1.
Proof.
  unfold ghcDisj, ghcValid.
  intros ?? H.
  repeat desf; try (by apply perm_disj_valid in H; desf).
Qed.
Lemma ghcDisj_valid_r :
  forall ghc1 ghc2, ghcDisj ghc1 ghc2 -> ghcValid ghc2.
Proof.
  intros ?? H. symmetry in H.
  by apply ghcDisj_valid_l in H.
Qed.
Lemma ghcDisj_valid :
  forall ghc1 ghc2,
  ghcDisj ghc1 ghc2 -> ghcValid ghc1 /\ ghcValid ghc2.
Proof.
  intros ghc1 ghc2 H. split.
  - by apply ghcDisj_valid_l in H.
  - by apply ghcDisj_valid_r in H.
Qed.


(** *** Union *)

(** The (disjoint) union of two permission heap cells
    is defined as the addition of their underlying
    fractional permissions. *)

(** [PHCfree] heap cells are neutral with respect to
    disjoint union, while [PHCinvalid] are absorbing. *)

Lemma val_pair_eq_dec :
  forall x y : Val * Val, {x = y} + {x <> y}.
Proof.
  decide equality; apply val_eq_dec.
Qed.

Definition phcUnion (phc1 phc2 : PermHeapCell) : PermHeapCell :=
  match phc1, phc2 with
    | PHCinvalid, _
    | _, PHCinvalid => PHCinvalid
    | PHCfree, phc
    | phc, PHCfree => phc
    | PHCstd q1 v1, PHCstd q2 v2 =>
        if val_eq_dec v1 v2
        then PHCstd (q1 + q2) v1
        else PHCinvalid
  end.

Notation "phc1 ⨄ phc2" :=
  (phcUnion phc1 phc2)
  (only printing, at level 80, right associativity).


Definition ghcUnion (ghc1 ghc2 : GuardHeapCell) : GuardHeapCell :=
  match ghc1, ghc2 with
    | GHCinvalid, _
    | _, GHCinvalid => GHCinvalid
    | GHCfree, ghc
    | ghc, GHCfree => ghc
    | GHCstd q1, GHCstd q2 =>
        GHCstd (q1 + q2)
  end.

Notation "ghc1 ⨄ ghc2" :=
  (ghcUnion ghc1 ghc2)
  (only printing, at level 80, right associativity).

(** The [phcUnion] relation is associative and commutative. *)

Lemma phcUnion_assoc :
  forall phc1 phc2 phc3,
  phcUnion phc1 (phcUnion phc2 phc3) =
  phcUnion (phcUnion phc1 phc2) phc3.
Proof.
  intros phc1 phc2 phc3.
  destruct phc1, phc2, phc3; simpls; desf;
    unfold phcUnion; desf; by rewrite Qcplus_assoc.
Qed.

Lemma phcUnion_comm :
  forall phc1 phc2,
  phcUnion phc1 phc2 = phcUnion phc2 phc1.
Proof.
  unfold phcUnion. ins.
  repeat desf; by rewrite Qcplus_comm.
Qed.

Hint Resolve phcUnion_assoc phcUnion_comm : core.


Lemma ghcUnion_assoc :
  forall ghc1 ghc2 ghc3,
  ghcUnion ghc1 (ghcUnion ghc2 ghc3) =
  ghcUnion (ghcUnion ghc1 ghc2) ghc3.
Proof.
  intros ghc1 ghc2 ghc3.
  destruct ghc1, ghc2, ghc3; simpls; desf;
    unfold ghcUnion; desf; by rewrite Qcplus_assoc.
Qed.

Lemma ghcUnion_comm :
  forall ghc1 ghc2,
  ghcUnion ghc1 ghc2 = ghcUnion ghc2 ghc1.
Proof.
  unfold ghcUnion. ins.
  repeat desf; by rewrite Qcplus_comm.
Qed.

Hint Resolve ghcUnion_assoc ghcUnion_comm : core.

(** The following lemmas show that [PHCfree] is neutral for union. *)

Lemma phcUnion_free_l :
  forall phc, phcUnion phc PHCfree = phc.
Proof. unfold phcUnion. ins. desf. Qed.
Lemma phcUnion_free_r :
  forall phc, phcUnion PHCfree phc = phc.
Proof. unfold phcUnion. ins. desf. Qed.

Hint Rewrite phcUnion_free_l phcUnion_free_r : core.


Lemma ghcUnion_free_l :
  forall ghc, ghcUnion ghc GHCfree = ghc.
Proof. unfold ghcUnion. ins. desf. Qed.
Lemma ghcUnion_free_r :
  forall ghc, ghcUnion GHCfree ghc = ghc.
Proof. unfold ghcUnion. ins. desf. Qed.

Hint Rewrite ghcUnion_free_l ghcUnion_free_r : core.

(** Below are various other useful properties of heap cell union. *)

Lemma phcUnion_valid :
  forall phc1 phc2,
  phcDisj phc1 phc2 -> phcValid (phcUnion phc1 phc2).
Proof.
  unfold phcDisj, phcUnion, phcValid.
  ins. repeat desf; by apply perm_add_valid.
Qed.

Lemma phcDisj_union_l :
  forall phc1 phc2 phc3,
  phcDisj phc1 phc2 ->
  phcDisj (phcUnion phc1 phc2) phc3 ->
  phcDisj phc2 phc3.
Proof.
  intros ??? H1 H2.
  unfold phcUnion, phcDisj in *.
  desf; simpls; intuition; permsolve.
Qed.
Lemma phcDisj_union_r :
  forall phc1 phc2 phc3,
  phcDisj phc2 phc3 ->
  phcDisj phc1 (phcUnion phc2 phc3) ->
  phcDisj phc1 phc2.
Proof.
  intros phc1 phc2 phc3 H1 H2.
  symmetry in H1, H2.
  rewrite phcUnion_comm in H2; auto.
  apply phcDisj_union_l in H2; auto.
  by symmetry.
Qed.

Lemma phcDisj_assoc_l :
  forall phc1 phc2 phc3,
  phcDisj phc1 phc2 ->
  phcDisj (phcUnion phc1 phc2) phc3 ->
  phcDisj phc1 (phcUnion phc2 phc3).
Proof.
  unfold phcDisj, phcUnion.
  intros phc1 phc2 phc3 H1 H2.
  desf; simpls; intuition vauto; permsolve.
Qed.
Lemma phcDisj_assoc_r :
  forall phc1 phc2 phc3,
  phcDisj phc2 phc3 ->
  phcDisj phc1 (phcUnion phc2 phc3) ->
  phcDisj (phcUnion phc1 phc2) phc3.
Proof.
  intros phc1 phc2 phc3 H1 H2.
  symmetry in H1, H2.
  rewrite phcUnion_comm in H2; auto.
  apply phcDisj_assoc_l in H2; auto.
  rewrite phcUnion_comm in H2; auto.
  by symmetry.
Qed.

Lemma phcDisj_middle :
  forall phc1 phc2 phc3 phc4,
  phcDisj phc1 phc2 ->
  phcDisj phc3 phc4 ->
  phcDisj (phcUnion phc1 phc2) (phcUnion phc3 phc4) ->
  phcDisj phc2 phc3.
Proof.
  intros phc1 phc2 phc3 phc4 H1 H2 H3.
  apply phcDisj_union_l with phc1; auto.
  by apply phcDisj_union_r with phc4.
Qed.

Lemma phcDisj_compat :
  forall phc1 phc2 phc3 phc4,
  phcDisj phc1 phc3 ->
  phcDisj phc2 phc4 ->
  phcDisj (phcUnion phc1 phc3) (phcUnion phc2 phc4) ->
  phcDisj (phcUnion phc1 phc2) (phcUnion phc3 phc4).
Proof.
  intros phc1 phc2 phc3 phc4 H1 H2 H3.
  apply phcDisj_assoc_r.
  rewrite phcUnion_comm.
  apply phcDisj_assoc_l; auto.
  symmetry. by apply phcDisj_union_l in H3.
  rewrite phcUnion_comm.
  rewrite <- phcUnion_assoc.
  apply phcDisj_assoc_l; auto.
  by rewrite phcUnion_comm with phc4 phc2.
Qed.

Lemma phcUnion_swap_l :
  forall phc1 phc2 phc3,
  phcUnion phc1 (phcUnion phc2 phc3) =
  phcUnion phc2 (phcUnion phc1 phc3).
Proof.
  intros phc1 phc2 phc3.
  rewrite phcUnion_assoc.
  rewrite phcUnion_comm with phc1 phc2.
  by rewrite phcUnion_assoc.
Qed.
Lemma phcUnion_swap_r :
  forall phc1 phc2 phc3,
  phcUnion (phcUnion phc1 phc2) phc3 =
  phcUnion (phcUnion phc1 phc3) phc2.
Proof.
  intros phc1 phc2 phc3.
  rewrite phcUnion_comm.
  rewrite phcUnion_swap_l.
  by rewrite phcUnion_assoc.
Qed.

Lemma phcUnion_compat :
  forall phc1 phc2 phc3 phc4,
  phcUnion (phcUnion phc1 phc3) (phcUnion phc2 phc4) =
  phcUnion (phcUnion phc1 phc2) (phcUnion phc3 phc4).
Proof.
  intros phc1 phc2 phc3 phc4.
  rewrite phcUnion_swap_l.
  repeat rewrite phcUnion_assoc.
  by rewrite phcUnion_comm with phc2 phc1.
Qed.

Lemma phcUnion_free :
  forall phc1 phc2,
  phcUnion phc1 phc2 = PHCfree <-> phc1 = PHCfree /\ phc2 = PHCfree.
Proof.
  intros phc1 phc2; split; intro H1.
  - unfold phcUnion in H1. desf.
  - destruct H1 as (H1&H2). clarify.
Qed.

Lemma phcUnion_not_free :
  forall phc1 phc2,
  phcUnion phc1 phc2 <> PHCfree <-> phc1 <> PHCfree \/ phc2 <> PHCfree.
Proof.
  intros phc1 phc2. split; intro H.
  - unfold phcUnion in H. desf; vauto.
  - unfold phcUnion. desf; vauto.
Qed.

Lemma ghcUnion_valid :
  forall ghc1 ghc2,
  ghcDisj ghc1 ghc2 -> ghcValid (ghcUnion ghc1 ghc2).
Proof.
  unfold ghcDisj, ghcUnion, ghcValid.
  ins. repeat desf; by apply perm_add_valid.
Qed.

Lemma ghcDisj_union_l :
  forall ghc1 ghc2 ghc3,
  ghcDisj ghc1 ghc2 ->
  ghcDisj (ghcUnion ghc1 ghc2) ghc3 ->
  ghcDisj ghc2 ghc3.
Proof.
  intros ??? H1 H2.
  unfold ghcUnion, ghcDisj in *.
  desf; simpls; intuition; permsolve.
Qed.
Lemma ghcDisj_union_r :
  forall ghc1 ghc2 ghc3,
  ghcDisj ghc2 ghc3 ->
  ghcDisj ghc1 (ghcUnion ghc2 ghc3) ->
  ghcDisj ghc1 ghc2.
Proof.
  intros ghc1 ghc2 ghc3 H1 H2.
  symmetry in H1, H2.
  rewrite ghcUnion_comm in H2; auto.
  apply ghcDisj_union_l in H2; auto.
  by symmetry.
Qed.

Lemma ghcDisj_assoc_l :
  forall ghc1 ghc2 ghc3,
  ghcDisj ghc1 ghc2 ->
  ghcDisj (ghcUnion ghc1 ghc2) ghc3 ->
  ghcDisj ghc1 (ghcUnion ghc2 ghc3).
Proof.
  unfold ghcDisj, ghcUnion.
  intros ghc1 ghc2 ghc3 H1 H2.
  desf; simpls; intuition vauto; permsolve.
Qed.
Lemma ghcDisj_assoc_r :
  forall ghc1 ghc2 ghc3,
  ghcDisj ghc2 ghc3 ->
  ghcDisj ghc1 (ghcUnion ghc2 ghc3) ->
  ghcDisj (ghcUnion ghc1 ghc2) ghc3.
Proof.
  intros ghc1 ghc2 ghc3 H1 H2.
  symmetry in H1, H2.
  rewrite ghcUnion_comm in H2; auto.
  apply ghcDisj_assoc_l in H2; auto.
  rewrite ghcUnion_comm in H2; auto.
  by symmetry.
Qed.

Lemma ghcDisj_middle :
  forall ghc1 ghc2 ghc3 ghc4,
  ghcDisj ghc1 ghc2 ->
  ghcDisj ghc3 ghc4 ->
  ghcDisj (ghcUnion ghc1 ghc2) (ghcUnion ghc3 ghc4) ->
  ghcDisj ghc2 ghc3.
Proof.
  intros ghc1 ghc2 ghc3 ghc4 H1 H2 H3.
  apply ghcDisj_union_l with ghc1; auto.
  by apply ghcDisj_union_r with ghc4.
Qed.

Lemma ghcDisj_compat :
  forall ghc1 ghc2 ghc3 ghc4,
  ghcDisj ghc1 ghc3 ->
  ghcDisj ghc2 ghc4 ->
  ghcDisj (ghcUnion ghc1 ghc3) (ghcUnion ghc2 ghc4) ->
  ghcDisj (ghcUnion ghc1 ghc2) (ghcUnion ghc3 ghc4).
Proof.
  intros ghc1 ghc2 ghc3 ghc4 H1 H2 H3.
  apply ghcDisj_assoc_r.
  rewrite ghcUnion_comm.
  apply ghcDisj_assoc_l; auto.
  symmetry. by apply ghcDisj_union_l in H3.
  rewrite ghcUnion_comm.
  rewrite <- ghcUnion_assoc.
  apply ghcDisj_assoc_l; auto.
  by rewrite ghcUnion_comm with ghc4 ghc2.
Qed.

Lemma ghcUnion_swap_l :
  forall ghc1 ghc2 ghc3,
  ghcUnion ghc1 (ghcUnion ghc2 ghc3) =
  ghcUnion ghc2 (ghcUnion ghc1 ghc3).
Proof.
  intros ghc1 ghc2 ghc3.
  rewrite ghcUnion_assoc.
  rewrite ghcUnion_comm with ghc1 ghc2.
  by rewrite ghcUnion_assoc.
Qed.
Lemma ghcUnion_swap_r :
  forall ghc1 ghc2 ghc3,
  ghcUnion (ghcUnion ghc1 ghc2) ghc3 =
  ghcUnion (ghcUnion ghc1 ghc3) ghc2.
Proof.
  intros ghc1 ghc2 ghc3.
  rewrite ghcUnion_comm.
  rewrite ghcUnion_swap_l.
  by rewrite ghcUnion_assoc.
Qed.

Lemma ghcUnion_compat :
  forall ghc1 ghc2 ghc3 ghc4,
  ghcUnion (ghcUnion ghc1 ghc3) (ghcUnion ghc2 ghc4) =
  ghcUnion (ghcUnion ghc1 ghc2) (ghcUnion ghc3 ghc4).
Proof.
  intros ghc1 ghc2 ghc3 ghc4.
  rewrite ghcUnion_swap_l.
  repeat rewrite ghcUnion_assoc.
  by rewrite ghcUnion_comm with ghc2 ghc1.
Qed.

Lemma ghcUnion_free :
  forall ghc1 ghc2,
  ghcUnion ghc1 ghc2 = GHCfree <-> ghc1 = GHCfree /\ ghc2 = GHCfree.
Proof.
  intros ghc1 ghc2; split; intro H1.
  - unfold ghcUnion in H1. desf.
  - destruct H1 as (H1&H2). clarify.
Qed.

Lemma ghcUnion_not_free :
  forall ghc1 ghc2,
  ghcUnion ghc1 ghc2 <> GHCfree <-> ghc1 <> GHCfree \/ ghc2 <> GHCfree.
Proof.
  intros ghc1 ghc2. split; intro H.
  - unfold ghcUnion in H. desf; vauto.
  - unfold ghcUnion. desf; vauto.
Qed.


(** *** Orderings *)

(** The following (strict) partial order defines the
    'less than' relation on permission heap cells. *)

Definition phcLt (phc1 phc2 : PermHeapCell) : Prop :=
  match phc1, phc2 with
    | PHCfree, PHCfree => False
    | PHCfree, _ => True
    | PHCstd q1 v1, PHCstd q2 v2 => q1 < q2 /\ v1 = v2
    | _, _ => False
  end.

Notation "phc1 ≺ phc2" :=
  (phcLt phc1 phc2)
  (only printing, at level 80).


Definition ghcLt (ghc1 ghc2 : GuardHeapCell) : Prop :=
  match ghc1, ghc2 with
    | GHCfree, GHCfree => False
    | GHCfree, _ => True
    | GHCstd q1, GHCstd q2 => q1 < q2
    | _, _ => False
  end.

Notation "ghc1 ≺ ghc2" :=
  (ghcLt ghc1 ghc2)
  (only printing, at level 80).

(** The [phcLt] relation is a strict partial order
    (i.e., irreflexive, asymmetric and transitive).  *)

Global Instance phcLt_irrefl : Irreflexive phcLt.
Proof.
  red. red. intros phc H.
  unfold phcLt in H. repeat desf.
  - by apply Qclt_irrefl with q.
Qed.
Global Instance phcLt_trans : Transitive phcLt.
Proof.
  red. intros phc1 phc2 phc3 H1 H2.
  unfold phcLt in *.
  repeat desf; intuition vauto.
  - by apply Qclt_trans with q1.
Qed.
Global Instance phcLt_asymm : Asymmetric phcLt.
Proof.
  red. intros phc1 phc2 H1 H2.
  assert (H3 : phcLt phc1 phc1) by by (transitivity phc2).
  by apply phcLt_irrefl in H3.
Qed.
Global Instance phcLt_strictorder : StrictOrder phcLt.
Proof. split; intuition. Qed.


Global Instance ghcLt_irrefl : Irreflexive ghcLt.
Proof.
  red. red. intros ghc H.
  unfold ghcLt in H. repeat desf.
  - by apply Qclt_irrefl with q.
Qed.
Global Instance ghcLt_trans : Transitive ghcLt.
Proof.
  red. intros ghc1 ghc2 ghc3 H1 H2.
  unfold ghcLt in *.
  repeat desf; intuition vauto.
  - by apply Qclt_trans with q1.
Qed.
Global Instance ghcLt_asymm : Asymmetric ghcLt.
Proof.
  red. intros ghc1 ghc2 H1 H2.
  assert (H3 : ghcLt ghc1 ghc1) by by (transitivity ghc2).
  by apply ghcLt_irrefl in H3.
Qed.
Global Instance ghcLt_strictorder : StrictOrder ghcLt.
Proof. split; intuition. Qed.

(** Below are several other useful properties of [phcLt]. *)

Lemma phcLt_mono_pos :
  forall phc1 phc2,
  phcDisj phc1 phc2 ->
  phcLt PHCfree phc2 ->
  phcLt phc1 (phcUnion phc1 phc2).
Proof.
  intros phc1 phc2 H1 H2.
  unfold phcDisj, phcValid in H1.
  unfold phcLt in *. unfold phcUnion.
  repeat desf; simpls; intuition vauto.
  - permsolve.
Qed.

Lemma phcLt_mono_l :
  forall phc1 phc2 phc3,
  phcDisj phc3 phc2 ->
  phcLt phc1 phc2 ->
  phcLt (phcUnion phc3 phc1) (phcUnion phc3 phc2).
Proof.
  intros phc1 phc2 phc3 H1 H2.
  destruct phc3; vauto.
  (* [phc3] is free *)
  - by repeat rewrite phcUnion_free_r.
  (* [phc3] is a standard heap cell *)
  - unfold phcDisj, phcUnion, phcLt in *.
    repeat desf; intuition.
    + permsolve.
    + clear H1. by apply Qcplus_lt_mono_l.
Qed.
Lemma phcLt_mono_r :
  forall phc1 phc2 phc3,
  phcDisj phc2 phc3 ->
  phcLt phc1 phc2 ->
  phcLt (phcUnion phc1 phc3) (phcUnion phc2 phc3).
Proof.
  intros phc1 phc2 phc3 H1 H2.
  rewrite phcUnion_comm with phc1 phc3.
  rewrite phcUnion_comm with phc2 phc3.
  apply phcLt_mono_l; auto. by symmetry.
Qed.

Lemma phcLt_diff :
  forall phc1 phc2,
  phcValid phc1 ->
  phcValid phc2 ->
  phcLt phc1 phc2 ->
  exists phc3, phcDisj phc1 phc3 /\ phcUnion phc1 phc3 = phc2.
Proof.
  intros phc1 phc2 H1 H2 H3.
  unfold phcValid in H1, H2.
  unfold phcLt in H3. repeat desf; vauto.
  (* [phc1] is free and [phc2] a 'standard' cell *)
  - exists (PHCstd q v). vauto.
  (* [phc1] and [phc2] are both 'standard' cells *)
  - apply perm_lt_diff in H3; auto.
    destruct H3 as (q'&H3&H4); vauto.
    exists (PHCstd q' v0). intuition vauto.
    unfold phcUnion. desf.
Qed.

Lemma phcDisj_lt :
  forall phc1 phc2 phc3,
  phcValid phc1 ->
  phcDisj phc2 phc3 ->
  phcLt phc1 phc2 ->
  phcDisj phc1 phc3.
Proof.
  intros phc1 phc2 phc3 H1 H2 H3.
  generalize H2. intros H4.
  apply phcDisj_valid in H4.
  destruct H4 as (H4&H5).
  unfold phcLt in H3.
  unfold phcDisj, phcValid in *.
  repeat desf; intuition vauto.
  - by apply perm_disj_lt with q1.
Qed.



Lemma ghcLt_mono_pos :
  forall ghc1 ghc2,
  ghcDisj ghc1 ghc2 ->
  ghcLt GHCfree ghc2 ->
  ghcLt ghc1 (ghcUnion ghc1 ghc2).
Proof.
  intros ghc1 ghc2 H1 H2.
  unfold ghcDisj, ghcValid in H1.
  unfold ghcLt in *. unfold ghcUnion.
  repeat desf; simpls; intuition vauto.
  - permsolve.
Qed.

Lemma ghcLt_mono_l :
  forall ghc1 ghc2 ghc3,
  ghcDisj ghc3 ghc2 ->
  ghcLt ghc1 ghc2 ->
  ghcLt (ghcUnion ghc3 ghc1) (ghcUnion ghc3 ghc2).
Proof.
  intros ghc1 ghc2 ghc3 H1 H2.
  destruct ghc3; vauto.
  (* [ghc3] is free *)
  - by repeat rewrite ghcUnion_free_r.
  (* [ghc3] is a standard heap cell *)
  - unfold ghcDisj, ghcUnion, ghcLt in *.
    repeat desf; intuition.
    + permsolve.
    + clear H1. by apply Qcplus_lt_mono_l.
Qed.
Lemma ghcLt_mono_r :
  forall ghc1 ghc2 ghc3,
  ghcDisj ghc2 ghc3 ->
  ghcLt ghc1 ghc2 ->
  ghcLt (ghcUnion ghc1 ghc3) (ghcUnion ghc2 ghc3).
Proof.
  intros ghc1 ghc2 ghc3 H1 H2.
  rewrite ghcUnion_comm with ghc1 ghc3.
  rewrite ghcUnion_comm with ghc2 ghc3.
  apply ghcLt_mono_l; auto. by symmetry.
Qed.

Lemma ghcLt_diff :
  forall ghc1 ghc2,
  ghcValid ghc1 ->
  ghcValid ghc2 ->
  ghcLt ghc1 ghc2 ->
  exists ghc3, ghcDisj ghc1 ghc3 /\ ghcUnion ghc1 ghc3 = ghc2.
Proof.
  intros ghc1 ghc2 H1 H2 H3.
  unfold ghcValid in H1, H2.
  unfold ghcLt in H3. repeat desf; vauto.
  (* [ghc1] is free and [ghc2] a 'standard' cell *)
  - exists (GHCstd q). vauto.
  (* [ghc1] and [ghc2] are both 'standard' cells *)
  - apply perm_lt_diff in H3; auto.
    destruct H3 as (q'&H3&H4); vauto.
    exists (GHCstd q'). intuition vauto.
Qed.

Lemma ghcDisj_lt :
  forall ghc1 ghc2 ghc3,
  ghcValid ghc1 ->
  ghcDisj ghc2 ghc3 ->
  ghcLt ghc1 ghc2 ->
  ghcDisj ghc1 ghc3.
Proof.
  intros ghc1 ghc2 ghc3 H1 H2 H3.
  generalize H2. intros H4.
  apply ghcDisj_valid in H4.
  destruct H4 as (H4&H5).
  unfold ghcLt in H3.
  unfold ghcDisj, ghcValid in *.
  repeat desf; intuition vauto.
  - by apply perm_disj_lt with q1.
Qed.

(** The following partial order defines the 'less than or equal to'
    relation on permission heap cells. *)

Definition phcLe (phc1 phc2 : PermHeapCell) : Prop :=
  match phc1, phc2 with
    | PHCfree, _ => True
    | PHCstd q1 v1, PHCstd q2 v2 => q1 <= q2 /\ v1 = v2
    | PHCinvalid, PHCinvalid => True
    | _, _ => False
  end.

Notation "phc1 ≼ phc2" :=
  (phcLe phc1 phc2)
  (only printing, at level 80).


Definition ghcLe (ghc1 ghc2 : GuardHeapCell) : Prop :=
  match ghc1, ghc2 with
    | GHCfree, _ => True
    | GHCstd q1, GHCstd q2 => q1 <= q2
    | GHCinvalid, GHCinvalid => True
    | _, _ => False
  end.

Notation "ghc1 ≼ ghc2" :=
  (ghcLe ghc1 ghc2)
  (only printing, at level 80).

(** The [phcLe] relation is a non-strict partial order. *)

Global Instance phcLe_refl : Reflexive phcLe.
Proof.
  red. intro phc. red.
  repeat desf; intuition vauto; by apply Qcle_refl.
Qed.

Hint Resolve phcLe_refl : core.

Lemma phcLt_le_weak :
  forall phc1 phc2,
  phcLt phc1 phc2 -> phcLe phc1 phc2.
Proof.
  intros phc1 phc2 H.
  unfold phcLt in H.
  unfold phcLe. repeat desf; intuition vauto.
  - by apply Qclt_le_weak.
Qed.

Lemma phcLe_lt_or_eq :
  forall phc1 phc2,
  phcLe phc1 phc2 <->
  phc1 = phc2 \/ phcLt phc1 phc2.
Proof.
  intros phc1 phc2. split; intro H.
  (* left-to-right *)
  - unfold phcLe in H. repeat desf; vauto.
    + destruct phc2; vauto.
    + apply Qcle_lt_or_eq in H. desf; vauto.
  (* right-to-left *)
  - destruct H as [H|H]; vauto.
    by apply phcLt_le_weak.
Qed.

Global Instance phcLe_antisym :
  Antisymmetric PermHeapCell eq phcLe.
Proof.
  red. intros phc1 phc2 H1 H2.
  apply phcLe_lt_or_eq in H1.
  apply phcLe_lt_or_eq in H2.
  destruct H1 as [H1|H1], H2 as [H2|H2]; vauto.
  by apply phcLt_asymm in H1.
Qed.
Global Instance phcLe_trans : Transitive phcLe.
Proof.
  red. intros phc1 phc2 phc3 H1 H2.
  apply phcLe_lt_or_eq in H1.
  apply phcLe_lt_or_eq in H2.
  destruct H1 as [H1|H1], H2 as [H2|H2]; vauto.
  - by apply phcLt_le_weak.
  - by apply phcLt_le_weak.
  - apply phcLt_le_weak.
    by transitivity phc2.
Qed.
Global Instance phcLe_preorder : PreOrder phcLe.
Proof. split; intuition. Qed.
Global Instance phcLe_partialorder : PartialOrder eq phcLe.
Proof.
  split.
  - intros H1. red. red. red. intuition vauto.
    red. auto.
  - intros H1. red in H1. red in H1. red in H1.
    destruct H1 as (H1&H2). red in H2.
    by apply phcLe_antisym.
Qed.


Global Instance ghcLe_refl : Reflexive ghcLe.
Proof.
  red. intro ghc. red.
  repeat desf; intuition vauto; by apply Qcle_refl.
Qed.

Hint Resolve ghcLe_refl : core.

Lemma ghcLt_le_weak :
  forall ghc1 ghc2,
  ghcLt ghc1 ghc2 -> ghcLe ghc1 ghc2.
Proof.
  intros ghc1 ghc2 H.
  unfold ghcLt in H.
  unfold ghcLe. repeat desf; intuition vauto.
  - by apply Qclt_le_weak.
Qed.

Lemma ghcLe_lt_or_eq :
  forall ghc1 ghc2,
  ghcLe ghc1 ghc2 <->
  ghc1 = ghc2 \/ ghcLt ghc1 ghc2.
Proof.
  intros ghc1 ghc2. split; intro H.
  (* left-to-right *)
  - unfold ghcLe in H. repeat desf; vauto.
    + destruct ghc2; vauto.
    + apply Qcle_lt_or_eq in H. desf; vauto.
  (* right-to-left *)
  - destruct H as [H|H]; vauto.
    by apply ghcLt_le_weak.
Qed.

Global Instance ghcLe_antisym :
  Antisymmetric GuardHeapCell eq ghcLe.
Proof.
  red. intros ghc1 ghc2 H1 H2.
  apply ghcLe_lt_or_eq in H1.
  apply ghcLe_lt_or_eq in H2.
  destruct H1 as [H1|H1], H2 as [H2|H2]; vauto.
  by apply ghcLt_asymm in H1.
Qed.
Global Instance ghcLe_trans : Transitive ghcLe.
Proof.
  red. intros ghc1 ghc2 ghc3 H1 H2.
  apply ghcLe_lt_or_eq in H1.
  apply ghcLe_lt_or_eq in H2.
  destruct H1 as [H1|H1], H2 as [H2|H2]; vauto.
  - by apply ghcLt_le_weak.
  - by apply ghcLt_le_weak.
  - apply ghcLt_le_weak.
    by transitivity ghc2.
Qed.
Global Instance ghcLe_preorder : PreOrder ghcLe.
Proof. split; intuition. Qed.
Global Instance ghcLe_partialorder : PartialOrder eq ghcLe.
Proof.
  split.
  - intros H1. red. red. red. intuition vauto.
    red. auto.
  - intros H1. red in H1. red in H1. red in H1.
    destruct H1 as (H1&H2). red in H2.
    by apply ghcLe_antisym.
Qed.

(** Below are various other useful properties of [phcLe]. *)

Lemma phcLe_valid :
  forall phc, phcLe PHCfree phc.
Proof.
  ins.
Qed.

Lemma phcLe_lt_trans :
  forall phc1 phc2 phc3,
  phcLe phc1 phc2 ->
  phcLt phc2 phc3 ->
  phcLt phc1 phc3.
Proof.
  intros phc1 phc2 phc3 H1 H2.
  apply phcLe_lt_or_eq in H1.
  destruct H1 as [H1|H1]; vauto.
  by transitivity phc2.
Qed.

Lemma phcLt_le_trans :
  forall phc1 phc2 phc3,
  phcLt phc1 phc2 ->
  phcLe phc2 phc3 ->
  phcLt phc1 phc3.
Proof.
  intros phc1 phc2 phc3 H1 H2.
  apply phcLe_lt_or_eq in H2.
  destruct H2 as [H2|H2]; vauto.
  by transitivity phc2.
Qed.

Lemma phcLt_weaken :
  forall phc1 phc2 phc3,
  phcDisj phc2 phc3 ->
  phcLt phc1 phc2 ->
  phcLt phc1 (phcUnion phc2 phc3).
Proof.
  intros phc1 phc2 phc3 H1 H2.
  apply phcLt_le_trans with phc2; auto.
  assert (H3 : PHCfree = phc3 \/ phcLt PHCfree phc3). {
    apply phcLe_lt_or_eq, phcLe_valid. }
  destruct H3 as [H3|H3].
  (* [phc3] is free *)
  - clarify. by rewrite phcUnion_free_l.
  (* [phc3] is occupied *)
  - rewrite phcLe_lt_or_eq. right.
    by apply phcLt_mono_pos.
Qed.

Lemma phcLe_weaken :
  forall phc1 phc2 phc3,
  phcDisj phc2 phc3 ->
  phcLe phc1 phc2 ->
  phcLe phc1 (phcUnion phc2 phc3).
Proof.
  intros phc1 phc2 phc3 H1 H2.
  apply phcLe_lt_or_eq in H2.
  destruct H2 as [H2|H2]; vauto.
  (* the 'equals' case *)
  - assert (H2 : PHCfree = phc3 \/ phcLt PHCfree phc3). {
      apply phcLe_lt_or_eq, phcLe_valid. }
    destruct H2 as [H2|H2].
    + clarify. by rewrite phcUnion_free_l.
    + apply phcLt_le_weak.
      by apply phcLt_mono_pos.
  (* the 'less than' case *)
  - by apply phcLt_le_weak, phcLt_weaken.
Qed.

Lemma phcLe_mono_l :
  forall phc1 phc2 phc3,
  phcDisj phc3 phc2 ->
  phcLe phc1 phc2 ->
  phcLe (phcUnion phc3 phc1) (phcUnion phc3 phc2).
Proof.
  intros phc1 phc2 phc3 H1 H2.
  apply phcLe_lt_or_eq in H2.
  destruct H2 as [H2|H2]; vauto.
  apply phcLt_le_weak.
  by apply phcLt_mono_l.
Qed.
Lemma phcLe_mono_r :
  forall phc1 phc2 phc3,
  phcDisj phc2 phc3 ->
  phcLe phc1 phc2 ->
  phcLe (phcUnion phc1 phc3) (phcUnion phc2 phc3).
Proof.
  intros phc1 phc2 phc3 H1 H2.
  rewrite phcUnion_comm with phc1 phc3.
  rewrite phcUnion_comm with phc2 phc3.
  apply phcLe_mono_l; auto.
  by symmetry.
Qed.

Lemma phcLe_mono_pos :
  forall phc1 phc2,
  phcDisj phc1 phc2 ->
  phcLe phc1 (phcUnion phc1 phc2).
Proof.
  intros phc1 phc2 H1.
  transitivity (phcUnion phc1 PHCfree).
  - by rewrite phcUnion_free_l.
  - apply phcLe_mono_l; vauto.
Qed.

Lemma phcLe_compat :
  forall phc1 phc2 phc3 phc4,
  phcDisj phc1 phc4 ->
  phcDisj phc3 phc4 ->
  phcLe phc1 phc3 ->
  phcLe phc2 phc4 ->
  phcLe (phcUnion phc1 phc2) (phcUnion phc3 phc4).
Proof.
  intros phc1 phc2 phc3 phc4.
  transitivity (phcUnion phc1 phc4).
  apply phcLe_mono_l; auto.
  apply phcLe_mono_r; auto.
Qed.

Lemma phcLe_diff :
  forall phc1 phc2,
  phcValid phc1 ->
  phcValid phc2 ->
  phcLe phc1 phc2 ->
  exists phc3, phcDisj phc1 phc3 /\ phcUnion phc1 phc3 = phc2.
Proof.
  intros phc1 phc2 H1 H2 H3.
  apply phcLe_lt_or_eq in H3.
  destruct H3 as [H3|H3]; clarify.
  (* the 'equals' case *)
  - exists PHCfree. split.
    + by apply phcDisj_free_l.
    + by rewrite phcUnion_free_l.
  (* the 'less than' case *)
  - apply phcLt_diff in H3; auto.
Qed.

Lemma phcDisj_le :
  forall phc1 phc2 phc3,
  phcValid phc1 ->
  phcDisj phc2 phc3 ->
  phcLe phc1 phc2 ->
  phcDisj phc1 phc3.
Proof.
  intros phc1 phc2 phc3 H1 H2 H3.
  apply phcLe_lt_or_eq in H3.
  destruct H3 as [H3|H3]; vauto.
  by apply phcDisj_lt with phc2.
Qed.



Lemma ghcLe_valid :
  forall ghc, ghcLe GHCfree ghc.
Proof.
  ins.
Qed.

Lemma ghcLe_lt_trans :
  forall ghc1 ghc2 ghc3,
  ghcLe ghc1 ghc2 ->
  ghcLt ghc2 ghc3 ->
  ghcLt ghc1 ghc3.
Proof.
  intros ghc1 ghc2 ghc3 H1 H2.
  apply ghcLe_lt_or_eq in H1.
  destruct H1 as [H1|H1]; vauto.
  by transitivity ghc2.
Qed.

Lemma ghcLt_le_trans :
  forall ghc1 ghc2 ghc3,
  ghcLt ghc1 ghc2 ->
  ghcLe ghc2 ghc3 ->
  ghcLt ghc1 ghc3.
Proof.
  intros ghc1 ghc2 ghc3 H1 H2.
  apply ghcLe_lt_or_eq in H2.
  destruct H2 as [H2|H2]; vauto.
  by transitivity ghc2.
Qed.

Lemma ghcLt_weaken :
  forall ghc1 ghc2 ghc3,
  ghcDisj ghc2 ghc3 ->
  ghcLt ghc1 ghc2 ->
  ghcLt ghc1 (ghcUnion ghc2 ghc3).
Proof.
  intros ghc1 ghc2 ghc3 H1 H2.
  apply ghcLt_le_trans with ghc2; auto.
  assert (H3 : GHCfree = ghc3 \/ ghcLt GHCfree ghc3). {
    apply ghcLe_lt_or_eq, ghcLe_valid. }
  destruct H3 as [H3|H3].
  (* [ghc3] is free *)
  - clarify. by rewrite ghcUnion_free_l.
  (* [ghc3] is occupied *)
  - rewrite ghcLe_lt_or_eq. right.
    by apply ghcLt_mono_pos.
Qed.

Lemma ghcLe_weaken :
  forall ghc1 ghc2 ghc3,
  ghcDisj ghc2 ghc3 ->
  ghcLe ghc1 ghc2 ->
  ghcLe ghc1 (ghcUnion ghc2 ghc3).
Proof.
  intros ghc1 ghc2 ghc3 H1 H2.
  apply ghcLe_lt_or_eq in H2.
  destruct H2 as [H2|H2]; vauto.
  (* the 'equals' case *)
  - assert (H2 : GHCfree = ghc3 \/ ghcLt GHCfree ghc3). {
      apply ghcLe_lt_or_eq, ghcLe_valid. }
    destruct H2 as [H2|H2].
    + clarify. by rewrite ghcUnion_free_l.
    + apply ghcLt_le_weak.
      by apply ghcLt_mono_pos.
  (* the 'less than' case *)
  - by apply ghcLt_le_weak, ghcLt_weaken.
Qed.

Lemma ghcLe_mono_l :
  forall ghc1 ghc2 ghc3,
  ghcDisj ghc3 ghc2 ->
  ghcLe ghc1 ghc2 ->
  ghcLe (ghcUnion ghc3 ghc1) (ghcUnion ghc3 ghc2).
Proof.
  intros ghc1 ghc2 ghc3 H1 H2.
  apply ghcLe_lt_or_eq in H2.
  destruct H2 as [H2|H2]; vauto.
  apply ghcLt_le_weak.
  by apply ghcLt_mono_l.
Qed.
Lemma ghcLe_mono_r :
  forall ghc1 ghc2 ghc3,
  ghcDisj ghc2 ghc3 ->
  ghcLe ghc1 ghc2 ->
  ghcLe (ghcUnion ghc1 ghc3) (ghcUnion ghc2 ghc3).
Proof.
  intros ghc1 ghc2 ghc3 H1 H2.
  rewrite ghcUnion_comm with ghc1 ghc3.
  rewrite ghcUnion_comm with ghc2 ghc3.
  apply ghcLe_mono_l; auto.
  by symmetry.
Qed.

Lemma ghcLe_mono_pos :
  forall ghc1 ghc2,
  ghcDisj ghc1 ghc2 ->
  ghcLe ghc1 (ghcUnion ghc1 ghc2).
Proof.
  intros ghc1 ghc2 H1.
  transitivity (ghcUnion ghc1 GHCfree).
  - by rewrite ghcUnion_free_l.
  - apply ghcLe_mono_l; vauto.
Qed.

Lemma ghcLe_compat :
  forall ghc1 ghc2 ghc3 ghc4,
  ghcDisj ghc1 ghc4 ->
  ghcDisj ghc3 ghc4 ->
  ghcLe ghc1 ghc3 ->
  ghcLe ghc2 ghc4 ->
  ghcLe (ghcUnion ghc1 ghc2) (ghcUnion ghc3 ghc4).
Proof.
  intros ghc1 ghc2 ghc3 ghc4.
  transitivity (ghcUnion ghc1 ghc4).
  apply ghcLe_mono_l; auto.
  apply ghcLe_mono_r; auto.
Qed.

Lemma ghcLe_diff :
  forall ghc1 ghc2,
  ghcValid ghc1 ->
  ghcValid ghc2 ->
  ghcLe ghc1 ghc2 ->
  exists ghc3, ghcDisj ghc1 ghc3 /\ ghcUnion ghc1 ghc3 = ghc2.
Proof.
  intros ghc1 ghc2 H1 H2 H3.
  apply ghcLe_lt_or_eq in H3.
  destruct H3 as [H3|H3]; clarify.
  (* the 'equals' case *)
  - exists GHCfree. split.
    + by apply ghcDisj_free_l.
    + by rewrite ghcUnion_free_l.
  (* the 'less than' case *)
  - apply ghcLt_diff in H3; auto.
Qed.

Lemma ghcDisj_le :
  forall ghc1 ghc2 ghc3,
  ghcValid ghc1 ->
  ghcDisj ghc2 ghc3 ->
  ghcLe ghc1 ghc2 ->
  ghcDisj ghc1 ghc3.
Proof.
  intros ghc1 ghc2 ghc3 H1 H2 H3.
  apply ghcLe_lt_or_eq in H3.
  destruct H3 as [H3|H3]; vauto.
  by apply ghcDisj_lt with ghc2.
Qed.


(** *** Entirety *)

(** Any permission heap cell [phc] is said to be _entire_
    if [phc] is occupied and holds a fractional permission [perm_full]. *)

Definition phcEntire (phc : PermHeapCell) : Prop :=
  match phc with
    | PHCfree
    | PHCinvalid => False
    | PHCstd q _ => q = perm_full
  end.


Definition ghcEntire (ghc : GuardHeapCell) : Prop :=
  match ghc with
    | GHCfree
    | GHCinvalid => False
    | GHCstd q => q = perm_full
  end.

Lemma phcEntire_union_l :
  forall phc1 phc2,
  phcDisj phc1 phc2 ->
  phcEntire phc1 ->
  phcEntire (phcUnion phc1 phc2).
Proof.
  intros phc1 phc2 H1 H2.
  unfold phcDisj in H1.
  unfold phcEntire in *.
  unfold phcUnion.
  desf; desf; permsolve.
Qed.
Lemma phcEntire_union_r :
  forall phc1 phc2,
  phcDisj phc1 phc2 ->
  phcEntire phc2 ->
  phcEntire (phcUnion phc1 phc2).
Proof.
  intros phc1 phc2 H1 H2. rewrite phcUnion_comm.
  apply phcEntire_union_l; auto.
  by symmetry.
Qed.
Lemma phcEntire_union :
  forall phc1 phc2,
  phcDisj phc1 phc2 ->
  phcEntire phc1 \/ phcEntire phc2 ->
  phcEntire (phcUnion phc1 phc2).
Proof.
  intros phc1 phc2 H1 H2.
  destruct H2 as [H2|H2].
  - by apply phcEntire_union_l.
  - by apply phcEntire_union_r.
Qed.

Lemma phcEntire_lt_neg :
  forall phc1 phc2,
  phcValid phc2 -> phcEntire phc1 -> ~ phcLt phc1 phc2.
Proof.
  intros phc1 phc2 H1 H2 H3.
  unfold phcValid in H1.
  unfold phcEntire in H2.
  unfold phcLt in H3. repeat desf.
  - permsolve.
Qed.

Lemma phcEntire_le :
  forall phc1 phc2,
  phcLe phc1 phc2 ->
  phcValid phc2 ->
  phcEntire phc1 ->
  phcEntire phc2.
Proof.
  intros phc1 phc2 H1 H2 H3.
  unfold phcValid, perm_valid in H2.
  unfold phcEntire, perm_full in *.
  desf; simpls; desf.
  - by apply Qcle_antisym.
Qed.

Lemma phcLe_entire_eq :
  forall phc1 phc2,
  phcValid phc2 ->
  phcEntire phc1 ->
  phcLe phc1 phc2 ->
  phc1 = phc2.
Proof.
  intros phc1 phc2 H1 H2 H3.
  apply phcLe_lt_or_eq in H3.
  destruct H3 as [H3|H3]; vauto.
  by apply phcEntire_lt_neg in H3.
Qed.

Lemma phcDisj_entire_free :
  forall phc1 phc2,
  phcDisj phc1 phc2 -> phcEntire phc1 -> phc2 = PHCfree.
Proof.
  intros phc1 phc2 H1 H2.
  unfold phcDisj in H1.
  unfold phcEntire in H2.
  repeat desf; permsolve.
Qed.

Lemma phcLt_entire_free :
  forall phc,
  phcEntire phc -> phcLt PHCfree phc.
Proof.
  intros phc H.
  unfold phcEntire in H.
  unfold phcLt. desf.
Qed.


Lemma ghcEntire_union_l :
  forall ghc1 ghc2,
  ghcDisj ghc1 ghc2 ->
  ghcEntire ghc1 ->
  ghcEntire (ghcUnion ghc1 ghc2).
Proof.
  intros ghc1 ghc2 H1 H2.
  unfold ghcDisj in H1.
  unfold ghcEntire in *.
  unfold ghcUnion.
  desf; desf; permsolve.
Qed.
Lemma ghcEntire_union_r :
  forall ghc1 ghc2,
  ghcDisj ghc1 ghc2 ->
  ghcEntire ghc2 ->
  ghcEntire (ghcUnion ghc1 ghc2).
Proof.
  intros ghc1 ghc2 H1 H2. rewrite ghcUnion_comm.
  apply ghcEntire_union_l; auto.
  by symmetry.
Qed.
Lemma ghcEntire_union :
  forall ghc1 ghc2,
  ghcDisj ghc1 ghc2 ->
  ghcEntire ghc1 \/ ghcEntire ghc2 ->
  ghcEntire (ghcUnion ghc1 ghc2).
Proof.
  intros ghc1 ghc2 H1 H2.
  destruct H2 as [H2|H2].
  - by apply ghcEntire_union_l.
  - by apply ghcEntire_union_r.
Qed.

Lemma ghcEntire_lt_neg :
  forall ghc1 ghc2,
  ghcValid ghc2 -> ghcEntire ghc1 -> ~ ghcLt ghc1 ghc2.
Proof.
  intros ghc1 ghc2 H1 H2 H3.
  unfold ghcValid in H1.
  unfold ghcEntire in H2.
  unfold ghcLt in H3. repeat desf.
  - permsolve.
Qed.

Lemma ghcEntire_le :
  forall ghc1 ghc2,
  ghcLe ghc1 ghc2 ->
  ghcValid ghc2 ->
  ghcEntire ghc1 ->
  ghcEntire ghc2.
Proof.
  intros ghc1 ghc2 H1 H2 H3.
  unfold ghcValid, perm_valid in H2.
  unfold ghcEntire, perm_full in *.
  desf; simpls; desf.
  - by apply Qcle_antisym.
Qed.

Lemma ghcLe_entire_eq :
  forall ghc1 ghc2,
  ghcValid ghc2 ->
  ghcEntire ghc1 ->
  ghcLe ghc1 ghc2 ->
  ghc1 = ghc2.
Proof.
  intros ghc1 ghc2 H1 H2 H3.
  apply ghcLe_lt_or_eq in H3.
  destruct H3 as [H3|H3]; vauto.
  by apply ghcEntire_lt_neg in H3.
Qed.

Lemma ghcDisj_entire_free :
  forall ghc1 ghc2,
  ghcDisj ghc1 ghc2 -> ghcEntire ghc1 -> ghc2 = GHCfree.
Proof.
  intros ghc1 ghc2 H1 H2.
  unfold ghcDisj in H1.
  unfold ghcEntire in H2.
  repeat desf; permsolve.
Qed.

Lemma ghcLt_entire_free :
  forall ghc,
  ghcEntire ghc -> ghcLt GHCfree ghc.
Proof.
  intros ghc H.
  unfold ghcEntire in H.
  unfold ghcLt. desf.
Qed.


(** *** Concretisation *)

(** The _concretisation_ of any permission heap cell [phc]
    is the underlying value of [phc] (thus removing all structure
    related to the context of the heap cell). *)

Definition phcConcr (phc : PermHeapCell) : option Val :=
  match phc with
    | PHCfree
    | PHCinvalid => None
    | PHCstd _ v => Some v
  end.

Lemma phcConcr_lt_none :
  forall phc1 phc2,
  phcLt phc1 phc2 ->
  phcConcr phc2 = None ->
  phcConcr phc1 = None.
Proof.
  intros phc1 phc2 H1 H2.
  unfold phcConcr in *. desf.
Qed.
Lemma phcConcr_le_none :
  forall phc1 phc2,
  phcLe phc1 phc2 ->
  phcConcr phc2 = None ->
  phcConcr phc1 = None.
Proof.
  intros phc1 phc2 H1 H2.
  apply phcLe_lt_or_eq in H1.
  destruct H1 as [H1|H1]; vauto.
  by apply phcConcr_lt_none in H1.
Qed.

Lemma phcConcr_lt_some :
  forall phc1 phc2 v,
  phcLt phc1 phc2 ->
  phcConcr phc1 = Some v ->
  phcConcr phc2 = Some v.
Proof.
  intros phc1 phc2 v H1 H2.
  unfold phcConcr in *.
  desf; simpls; desf.
Qed.
Lemma phcConcr_le_some :
  forall phc1 phc2 v,
  phcLe phc1 phc2 ->
  phcConcr phc1 = Some v ->
  phcConcr phc2 = Some v.
Proof.
  intros phc1 phc2 v H1 H2.
  apply phcLe_lt_or_eq in H1.
  destruct H1 as [H1|H1]; vauto.
  by apply phcConcr_lt_some with (v:=v) in H1.
Qed.

Lemma phcConcr_none_free :
  forall phc,
  phcValid phc -> phcConcr phc = None -> phc = PHCfree.
Proof.
  intros phc H1 H2.
  unfold phcValid in H1.
  unfold phcConcr in H2. desf.
Qed.

Lemma phcConcr_union :
  forall phc1 phc2 v,
  phcDisj phc1 phc2 ->
  phcConcr phc1 = Some v ->
  phcConcr (phcUnion phc1 phc2) = Some v.
Proof.
  intros phc1 phc2 v H1 H2.
  apply phcConcr_le_some with phc1; vauto.
  by apply phcLe_mono_pos.
Qed.

Lemma phcConcr_compat :
  forall phc1 phc2 phc3 phc4,
  phcDisj phc1 phc2 ->
  phcDisj phc3 phc4 ->
  phcConcr phc1 = phcConcr phc3 ->
  phcConcr phc2 = phcConcr phc4 ->
  phcConcr (phcUnion phc1 phc2) = phcConcr (phcUnion phc3 phc4).
Proof.
  intros phc1 phc2 phc3 phc4 D1 D2 H1 H2.
  unfold phcDisj, phcUnion in *.
  repeat desf; vauto.
Qed.

Lemma phcConcr_disj_union_l :
  forall phc1 phc2 phc3,
  phcDisj phc1 phc3 ->
  phcDisj phc2 phc3 ->
  phcConcr phc1 = phcConcr phc2 ->
  phcConcr (phcUnion phc1 phc3) = phcConcr (phcUnion phc2 phc3).
Proof.
  intros phc1 phc2 phc3 H1 H2 H3.
  apply phcConcr_compat; vauto.
Qed.
Lemma phcConcr_disj_union_r :
  forall phc1 phc2 phc3,
  phcDisj phc1 phc3 ->
  phcDisj phc2 phc3 ->
  phcConcr phc1 = phcConcr phc2 ->
  phcConcr (phcUnion phc3 phc1) = phcConcr (phcUnion phc3 phc2).
Proof.
  intros phc1 phc2 phc3 H1 H2 H3.
  rewrite phcUnion_comm with phc3 phc1.
  rewrite phcUnion_comm with phc3 phc2.
  apply phcConcr_disj_union_l; auto.
Qed.


(** *** Snapshots *)

(** The following operation extracts the _snapshot value_
    out of a given permission heap cell. *)

Definition phcSnapshot (phc : PermHeapCell) : option Val :=
  match phc with
    | PHCfree
    | PHCinvalid
    | PHCstd _ _  => None
  end.

(** Below are several useful properties of snapshot extraction. *)

Lemma phcSnapshot_compat :
  forall phc1 phc2 phc3 phc4,
  phcDisj phc1 phc2 ->
  phcDisj phc3 phc4 ->
  phcSnapshot phc1 = phcSnapshot phc3 ->
  phcSnapshot phc2 = phcSnapshot phc4 ->
  phcSnapshot (phcUnion phc1 phc2) = phcSnapshot (phcUnion phc3 phc4).
Proof.
  intros phc1 phc2 phc3 phc4 D1 D2 H1 H2.
  unfold phcDisj, phcUnion in *.
  repeat desf; vauto.
Qed.

Lemma phcConcr_snapshot_compat :
  forall phc1 phc2 phc3 phc4,
  phcDisj phc1 phc2 ->
  phcDisj phc3 phc4 ->
  phcConcr phc1 = phcSnapshot phc3 ->
  phcConcr phc2 = phcSnapshot phc4 ->
  phcConcr (phcUnion phc1 phc2) = phcSnapshot (phcUnion phc3 phc4).
Proof.
  intros phc1 phc2 phc3 phc4 D1 D2 H1 H2.
  unfold phcDisj, phcUnion in *.
  repeat desf; vauto.
Qed.

Lemma phcSnapshot_disj_union_l :
  forall phc1 phc2 phc3,
  phcDisj phc1 phc3 ->
  phcDisj phc2 phc3 ->
  phcSnapshot phc1 = phcSnapshot phc2 ->
  phcSnapshot (phcUnion phc1 phc3) = phcSnapshot (phcUnion phc2 phc3).
Proof.
  intros phc1 phc2 phc3 H1 H2 H3.
  apply phcSnapshot_compat; vauto.
Qed.
Lemma phcSnapshot_disj_union_r :
  forall phc1 phc2 phc3,
  phcDisj phc1 phc3 ->
  phcDisj phc2 phc3 ->
  phcSnapshot phc1 = phcSnapshot phc2 ->
  phcSnapshot (phcUnion phc3 phc1) = phcSnapshot (phcUnion phc3 phc2).
Proof.
  intros phc1 phc2 phc3 H1 H2 H3.
  rewrite phcUnion_comm with phc3 phc1.
  rewrite phcUnion_comm with phc3 phc2.
  apply phcSnapshot_disj_union_l; auto.
Qed.

Lemma phcSnapshot_lt_none :
  forall phc1 phc2,
  phcLt phc1 phc2 ->
  phcSnapshot phc2 = None ->
  phcSnapshot phc1 = None.
Proof.
  intros phc1 phc2 H1 H2.
  unfold phcSnapshot in *. desf.
Qed.
Lemma phcSnapshot_le_none :
  forall phc1 phc2,
  phcLe phc1 phc2 ->
  phcSnapshot phc2 = None ->
  phcSnapshot phc1 = None.
Proof.
  intros phc1 phc2 H1 H2.
  apply phcLe_lt_or_eq in H1.
  destruct H1 as [H1|H1]; vauto.
  by apply phcSnapshot_lt_none in H1.
Qed.

Lemma phcSnapshot_lt_some :
  forall phc1 phc2 v,
  phcLt phc1 phc2 ->
  phcSnapshot phc1 = Some v ->
  phcSnapshot phc2 = Some v.
Proof.
  intros phc1 phc2 v H1 H2.
  unfold phcSnapshot in *.
  desf; simpls; desf.
Qed.
Lemma phcSnapshot_le_some :
  forall phc1 phc2 v,
  phcLe phc1 phc2 ->
  phcSnapshot phc1 = Some v ->
  phcSnapshot phc2 = Some v.
Proof.
  intros phc1 phc2 v H1 H2.
  apply phcLe_lt_or_eq in H1.
  destruct H1 as [H1|H1]; vauto.
  by apply phcSnapshot_lt_some with (v:=v) in H1.
Qed.

Lemma phcSnapshot_union :
  forall phc1 phc2 v,
  phcDisj phc1 phc2 ->
  phcSnapshot phc1 = Some v ->
  phcSnapshot (phcUnion phc1 phc2) = Some v.
Proof.
  intros phc1 phc2 v H1 H2.
  apply phcSnapshot_le_some with phc1; vauto.
  by apply phcLe_mono_pos.
Qed.


(** *** Heap cell conversion *)

(** Below are three operations for converting the
    type of permission heap cells, named
    [phcConvStd], for converting to standard heap cells;
    [phcConvProc], for converting to process heap cells;
    and [phcConvAct], for converting to action heap cells. *)

Definition phcConvStd (phc : PermHeapCell) : PermHeapCell :=
  match phc with
    | PHCfree => PHCfree
    | PHCstd q v => PHCstd q v
    | PHCinvalid => PHCinvalid
  end.

Notation "'std' { phc }" :=
  (phcConvStd phc)
  (only printing, at level 40).

(** Converting any heap cell to its original types does not
    have any effect. *)

Lemma phc_std_conv :
  forall q v, PHCstd q v = phcConvStd (PHCstd q v).
Proof. ins. Qed.

(** Heap cell conversion is idempotent. *)

Lemma phcConvStd_idemp :
  forall phc, phcConvStd (phcConvStd phc) = phcConvStd phc.
Proof. intro phc. unfold phcConvStd. desf. Qed.

(** Free heap cells always convert to free heap cells. *)

Lemma phcConvStd_free :
  phcConvStd PHCfree = PHCfree.
Proof. ins. Qed.
Lemma phcConvStd_free2 :
  forall phc, phcConvStd phc = PHCfree <-> phc = PHCfree.
Proof. unfold phcConvStd. intuition desf. Qed.

(** Invalid heap cells always convert to invalid heap cells. *)

Lemma phcConvStd_invalid :
  phcConvStd PHCinvalid = PHCinvalid.
Proof. ins. Qed.
Lemma phcConvStd_invalid2 :
  forall phc, phcConvStd phc = PHCinvalid <-> phc = PHCinvalid.
Proof. unfold phcConvStd. intuition desf. Qed.

(** Heap cell conversion preserves validity. *)

Lemma phcConvStd_valid :
  forall phc, phcValid phc <-> phcValid (phcConvStd phc).
Proof. ins. unfold phcValid, phcConvStd. intuition desf. Qed.

(** Heap cell conversion preserves disjointness. *)

Add Parametric Morphism : phcConvStd
  with signature phcDisj ==> phcDisj as phcConvStd_disj.
Proof.
  ins. unfold phcDisj in *. unfold phcConvStd.
  repeat desf; intuition simpls; auto.
Qed.

(** Heap cell conversion preserves entirety. *)

Lemma phcConvStd_entire :
  forall phc, phcEntire (phcConvStd phc) <-> phcEntire phc.
Proof. ins. unfold phcEntire, phcConvStd. intuition desf. Qed.

(** Below are several other properties of heap cell conversion
    for later convenience. *)

(** Note: in the following three lemmas, the validity condition
    is not neccessary for the right-to-left implication. *)

Lemma phcLt_conv_std_disj :
  forall phc2 phc3 q v,
  phcValid phc2 ->
  phcLt (PHCstd q v) phc2 ->
  phcDisj (phcConvStd phc2) phc3 <-> phcDisj phc2 phc3.
Proof.
  intros phc2 phc3 q v V1 H1. split; intro H2.
  - unfold phcConvStd in H2. unfold phcDisj in *.
    repeat desf; simpls; intuition vauto.
  - unfold phcConvStd. unfold phcDisj in *.
    repeat desf; simpls; intuition vauto.
Qed.

Lemma phcLe_conv_std_disj :
  forall phc2 phc3 q v,
  phcValid phc2 ->
  phcLe (PHCstd q v) phc2 ->
  phcDisj (phcConvStd phc2) phc3 <-> phcDisj phc2 phc3.
Proof.
  intros phc2 phc3 q v V1 H1. split; intro D1.
  - unfold phcConvStd in D1. unfold phcDisj in *.
    repeat desf; simpls; intuition vauto.
  - unfold phcConvStd. unfold phcDisj in *.
    repeat desf; simpls; intuition vauto.
Qed.

Lemma phcConvStd_disj_entire :
  forall phc1 phc2,
  phcEntire phc1 ->
  phcDisj phc1 phc2 ->
  phcDisj (phcConvStd phc1) phc2.
Proof.
  intros phc1 phc2 H1 H2.
  assert (H3 : phcValid phc1) by by apply phcDisj_valid_l in H2.
  apply phcDisj_entire_free in H2; auto. clarify.
  replace PHCfree with (phcConvStd PHCfree); auto.
  by apply phcConvStd_disj, phcDisj_free_r.
Qed.

Lemma phcConvStd_union :
  forall phc1 phc2,
  phcDisj phc1 phc2 ->
  phcConvStd (phcUnion phc1 phc2) =
  phcUnion (phcConvStd phc1) (phcConvStd phc2).
Proof.
  intros phc1 phc2 H. unfold phcDisj in H.
  unfold phcConvStd, phcUnion. repeat desf.
Qed.

Lemma phcConvStd_lt :
  forall phc1 phc2,
  phcValid phc2 ->
  phcLt phc1 phc2 ->
  phcLt (phcConvStd phc1) (phcConvStd phc2).
Proof.
  intros phc1 phc2 H1 H2.
  unfold phcValid in H1.
  unfold phcConvStd, phcLt in *.
  repeat desf.
Qed.

Lemma phcConvStd_le :
  forall phc1 phc2,
  phcValid phc2 ->
  phcLe phc1 phc2 ->
  phcLe (phcConvStd phc1) (phcConvStd phc2).
Proof.
  intros phc1 phc2 H1 H2.
  apply phcLe_lt_or_eq in H2.
  destruct H2 as [H2|H2]; vauto.
  by apply phcLt_le_weak, phcConvStd_lt.
Qed.

Lemma phcConvStd_concr :
  forall phc, phcConcr (phcConvStd phc) = phcConcr phc.
Proof. ins. unfold phcConcr, phcConvStd. desf. Qed.

Lemma phcSnapshot_lt_conv_std :
  forall phc1 phc2,
  phcLt phc1 (phcConvStd phc2) ->
  phcSnapshot phc1 = phcSnapshot (phcConvStd phc1).
Proof.
  intros phc1 phc2 H1. unfold phcConvStd in *.
  unfold phcLt in H1. unfold phcSnapshot. desf.
Qed.

(** Note: the following lemmas does not hold
    for process or action heap cell conversion. *)

Lemma phcConvStd_lt_eq :
  forall q v phc,
  phcLt (PHCstd q v) phc -> phc = phcConvStd phc.
Proof.
  intros q v phc H1. unfold phcConvStd in *.
  unfold phcLt in H1. desf.
Qed.


(** ** Permission heaps *)

(** Permission heaps are defined as (total) mappings
    from values to permission heap cells. *)

Definition PermHeap := Val -> PermHeapCell.

Inductive Guard :=
  | GGuard(t a: Val).

Lemma guard_eq_dec :
    forall x y : Guard, {x = y} + {x <> y}.
Proof.
  decide equality; apply val_eq_dec.
Qed.

Definition GuardHeap := Guard -> GuardHeapCell.

(** The identity permission heap is free at every location *)

Definition phIden : PermHeap := fun _ => PHCfree.

Definition ghIden : GuardHeap := fun _ => GHCfree.

(** An update operation for process maps: *)

Definition phUpdate (ph : PermHeap)(v : Val)(c : PermHeapCell) :=
  update val_eq_dec ph v c.


Definition ghUpdate (gh : GuardHeap)(v : Guard)(c : GuardHeapCell) :=
  update guard_eq_dec gh v c.

(** *** Validity *)

(** Any permission heap [ph] is defined to be _valid_
    if every entry of [ph] is valid. *)

Definition phValid (ph : PermHeap) : Prop :=
  forall l, phcValid (ph l).

Notation "√ ph" :=
  (phValid ph)
  (only printing, at level 80).


Definition ghValid (gh : GuardHeap) : Prop :=
  forall l, ghcValid (gh l).

Notation "√ gh" :=
  (ghValid gh)
  (only printing, at level 80).

(** The identity permission heap is valid. *)

Lemma phValid_iden : phValid phIden.
Proof. red. ins. Qed.

Hint Resolve phValid_iden : core.


Lemma ghValid_iden : ghValid ghIden.
Proof. red. ins. Qed.

Hint Resolve ghValid_iden : core.

(** Updating a valid permission heap with a valid entry
    results in a valid permission heap. *)

Lemma phValid_update :
  forall ph phc l,
  phValid ph -> phcValid phc -> phValid (phUpdate ph l phc).
Proof.
  intros ??????. unfold phUpdate, update. desf.
Qed.


Lemma ghValid_update :
  forall gh ghc l,
  ghValid gh -> ghcValid ghc -> ghValid (ghUpdate gh l ghc).
Proof.
  intros ??????. unfold ghUpdate, update. desf.
Qed.


(** *** Disjointness *)

(** Any two permission heaps are said to be _disjoint_
    if all their entries are pairwise disjoint. *)

Definition phDisj : relation PermHeap :=
  pointwise_relation Val phcDisj.

Notation "ph1 ⟂ ph2" :=
  (phDisj ph1 ph2)
  (only printing, at level 80).


Definition ghDisj : relation GuardHeap :=
  pointwise_relation Guard ghcDisj.

Notation "gh1 ⟂ gh2" :=
  (ghDisj gh1 gh2)
  (only printing, at level 80).

(** Permission heap disjointness is symmeric. *)

Global Instance phDisj_symm : Symmetric phDisj.
Proof. intros ????. by symmetry. Qed.

Global Instance ghDisj_symm : Symmetric ghDisj.
Proof. intros ????. by symmetry. Qed.

(** Permission heap disjointness implies validity. *)

Lemma phDisj_valid_l :
  forall ph1 ph2, phDisj ph1 ph2 -> phValid ph1.
Proof. intros ? ph ? l. by apply phcDisj_valid_l with (ph l). Qed.
Lemma phDisj_valid_r :
  forall ph1 ph2, phDisj ph1 ph2 -> phValid ph2.
Proof. intros ph ?? l. by apply phcDisj_valid_r with (ph l). Qed.
Lemma phDisj_valid :
  forall ph1 ph2, phDisj ph1 ph2 -> phValid ph1 /\ phValid ph2.
Proof.
  intros ph1 ph2 H. split.
  - by apply phDisj_valid_l with ph2.
  - by apply phDisj_valid_r with ph1.
Qed.


Lemma ghDisj_valid_l :
  forall gh1 gh2, ghDisj gh1 gh2 -> ghValid gh1.
Proof. intros ? gh ? l. by apply ghcDisj_valid_l with (gh l). Qed.
Lemma ghDisj_valid_r :
  forall gh1 gh2, ghDisj gh1 gh2 -> ghValid gh2.
Proof. intros gh ?? l. by apply ghcDisj_valid_r with (gh l). Qed.
Lemma ghDisj_valid :
  forall gh1 gh2, ghDisj gh1 gh2 -> ghValid gh1 /\ ghValid gh2.
Proof.
  intros gh1 gh2 H. split.
  - by apply ghDisj_valid_l with gh2.
  - by apply ghDisj_valid_r with gh1.
Qed.

(** Any valid permission heap is disjoint
    with the identity permission heap. *)

Lemma phDisj_iden_l :
  forall ph, phValid ph -> phDisj ph phIden.
Proof.
  unfold phValid, phIden.
  intros ???. by apply phcDisj_free_l.
Qed.
Lemma phDisj_iden_r :
  forall ph, phValid ph -> phDisj phIden ph.
Proof.
  unfold phValid, phIden.
  intros ???. by apply phcDisj_free_r.
Qed.

Hint Resolve phDisj_iden_l phDisj_iden_r : core.


Lemma ghDisj_iden_l :
  forall gh, ghValid gh -> ghDisj gh ghIden.
Proof.
  unfold ghValid, ghIden.
  intros ???. by apply ghcDisj_free_l.
Qed.
Lemma ghDisj_iden_r :
  forall gh, ghValid gh -> ghDisj ghIden gh.
Proof.
  unfold ghValid, ghIden.
  intros ???. by apply ghcDisj_free_r.
Qed.

Hint Resolve ghDisj_iden_l ghDisj_iden_r : core.

(** Updating disjoint permission heaps with entries
    that are disjoint preserves heap disjointness. *)

Lemma phDisj_upd :
  forall ph1 ph2 phc1 phc2 l,
  phcDisj phc1 phc2 ->
  phDisj ph1 ph2 ->
  phDisj (phUpdate ph1 l phc1) (phUpdate ph2 l phc2).
Proof.
  unfold phDisj, phUpdate, update.
  intros ????????. desf.
Qed.

Add Parametric Morphism : phUpdate
  with signature phDisj ==> eq ==> phcDisj ==> phDisj
    as phDisj_upd_mor.
Proof.
  intros ph1 ph1' H1 v ph2 ph2' H2.
  by apply phDisj_upd.
Qed.


Lemma ghDisj_upd :
  forall gh1 gh2 ghc1 ghc2 l,
  ghcDisj ghc1 ghc2 ->
  ghDisj gh1 gh2 ->
  ghDisj (ghUpdate gh1 l ghc1) (ghUpdate gh2 l ghc2).
Proof.
  unfold phDisj, ghUpdate, update.
  intros ????????. desf.
Qed.

Add Parametric Morphism : ghUpdate
  with signature ghDisj ==> eq ==> ghcDisj ==> ghDisj
    as ghDisj_upd_mor.
Proof.
  intros gh1 gh1' H1 v gh2 gh2' H2.
  by apply ghDisj_upd.
Qed.


(** *** Union *)

(** The (disjoint) union of two permission heaps is defined
    to be the pairwise disjoint union of their heap cells. *)

Definition phUnion (ph1 ph2 : PermHeap) : PermHeap :=
  fun l => phcUnion (ph1 l) (ph2 l).

Notation "ph1 ⨄ ph2" :=
  (phUnion ph1 ph2)
  (only printing, at level 80, right associativity).


Definition ghUnion (gh1 gh2 : GuardHeap) : GuardHeap :=
  fun l => ghcUnion (gh1 l) (gh2 l).

Notation "gh1 ⨄ gh2" :=
  (ghUnion gh1 gh2)
  (only printing, at level 80, right associativity).

(** Identity laws for disjoint union. *)

Lemma phUnion_iden_l :
  forall ph, phUnion ph phIden = ph.
Proof.
  intro ph. extensionality l.
  unfold phUnion, phIden.
  apply phcUnion_free_l.
Qed.
Lemma phUnion_iden_r :
  forall ph, phUnion phIden ph = ph.
Proof.
  intro ph. extensionality l.
  unfold phUnion, phIden.
  apply phcUnion_free_r.
Qed.

Hint Rewrite phUnion_iden_l phUnion_iden_r : core.


Lemma ghUnion_iden_l :
  forall gh, ghUnion gh ghIden = gh.
Proof.
  intro gh. extensionality l.
  unfold ghUnion, ghIden.
  apply ghcUnion_free_l.
Qed.
Lemma ghUnion_iden_r :
  forall gh, ghUnion ghIden gh = gh.
Proof.
  intro gh. extensionality l.
  unfold ghUnion, ghIden.
  apply ghcUnion_free_r.
Qed.

Hint Rewrite ghUnion_iden_l ghUnion_iden_r : core.

(** Disjoint union is associative and commutative. *)

Lemma phUnion_assoc :
  forall ph1 ph2 ph3,
  phUnion (phUnion ph1 ph2) ph3 = phUnion ph1 (phUnion ph2 ph3).
Proof.
  intros ???. extensionality l.
  unfold phUnion.
  by rewrite phcUnion_assoc.
Qed.

Lemma phUnion_comm :
  forall ph1 ph2, phUnion ph1 ph2 = phUnion ph2 ph1.
Proof.
  intros ??. extensionality l.
  by apply phcUnion_comm.
Qed.


Lemma ghUnion_assoc :
  forall gh1 gh2 gh3,
  ghUnion (ghUnion gh1 gh2) gh3 = ghUnion gh1 (ghUnion gh2 gh3).
Proof.
  intros ???. extensionality l.
  unfold ghUnion.
  by rewrite ghcUnion_assoc.
Qed.

Lemma ghUnion_comm :
  forall gh1 gh2, ghUnion gh1 gh2 = ghUnion gh2 gh1.
Proof.
  intros ??. extensionality l.
  by apply ghcUnion_comm.
Qed.

(** The union of any two disjoint permission heaps is valid. *)

Lemma phUnion_valid :
  forall ph1 ph2,
  phDisj ph1 ph2 -> phValid (phUnion ph1 ph2).
Proof.
  unfold phUnion. intros ????.
  by apply phcUnion_valid.
Qed.

Hint Resolve phUnion_valid : core.


Lemma ghUnion_valid :
  forall gh1 gh2,
  ghDisj gh1 gh2 -> ghValid (ghUnion gh1 gh2).
Proof.
  unfold ghUnion. intros ????.
  by apply ghcUnion_valid.
Qed.

Hint Resolve ghUnion_valid : core.

(** Below are various other useful properties of disjoint union. *)

Lemma phDisj_union_l :
  forall ph1 ph2 ph3,
  phDisj ph1 ph2 ->
  phDisj (phUnion ph1 ph2) ph3 ->
  phDisj ph2 ph3.
Proof.
  intros ph1 ph2 ph3 H1 H2 l.
  apply phcDisj_union_l with (ph1 l); auto.
  by apply H2.
Qed.
Lemma phDisj_union_r :
  forall ph1 ph2 ph3,
  phDisj ph2 ph3 ->
  phDisj ph1 (phUnion ph2 ph3) ->
  phDisj ph1 ph2.
Proof.
  intros ph1 ph2 ph3 H1 H2 l.
  apply phcDisj_union_r with (ph3 l); auto.
  by apply H2.
Qed.

Lemma phDisj_assoc_l :
  forall ph1 ph2 ph3,
  phDisj ph1 ph2 ->
  phDisj (phUnion ph1 ph2) ph3 ->
  phDisj ph1 (phUnion ph2 ph3).
Proof.
  intros ???? H ?.
  apply phcDisj_assoc_l. auto. apply H.
Qed.
Lemma phDisj_assoc_r :
  forall ph1 ph2 ph3,
  phDisj ph2 ph3 ->
  phDisj ph1 (phUnion ph2 ph3) ->
  phDisj (phUnion ph1 ph2) ph3.
Proof.
  intros ???? H ?.
  apply phcDisj_assoc_r. auto. apply H.
Qed.

Lemma phUnion_update :
  forall ph1 ph2 phc1 phc2 l,
  phUpdate (phUnion ph1 ph2) l (phcUnion phc1 phc2) =
  phUnion (phUpdate ph1 l phc1) (phUpdate ph2 l phc2).
Proof.
  ins. extensionality l'.
  unfold phUnion, phUpdate, update. desf.
Qed.

Lemma phUnion_cell :
  forall ph1 ph2 l,
  phcUnion (ph1 l) (ph2 l) = phUnion ph1 ph2 l.
Proof. ins. Qed.

Lemma phDisj_middle :
  forall ph1 ph2 ph3 ph4,
  phDisj ph1 ph2 ->
  phDisj ph3 ph4 ->
  phDisj (phUnion ph1 ph2) (phUnion ph3 ph4) ->
  phDisj ph2 ph3.
Proof.
  intros ph1 ph2 ph3 ph4 H1 H2 H3.
  apply phDisj_union_l with ph1; auto.
  by apply phDisj_union_r with ph4.
Qed.

Lemma phDisj_compat :
  forall ph1 ph2 ph3 ph4,
  phDisj ph1 ph3 ->
  phDisj ph2 ph4 ->
  phDisj (phUnion ph1 ph3) (phUnion ph2 ph4) ->
  phDisj (phUnion ph1 ph2) (phUnion ph3 ph4).
Proof.
  intros ph1 ph2 ph3 ph4 H1 H2 H3.
  apply phDisj_assoc_r.
  rewrite phUnion_comm.
  apply phDisj_assoc_l; auto.
  symmetry. by apply phDisj_union_l in H3.
  rewrite phUnion_comm.
  rewrite phUnion_assoc.
  apply phDisj_assoc_l; auto.
  by rewrite phUnion_comm with ph4 ph2.
Qed.

Lemma phUnion_swap_l :
  forall ph1 ph2 ph3,
  phUnion ph1 (phUnion ph2 ph3) =
  phUnion ph2 (phUnion ph1 ph3).
Proof.
  intros ph1 ph2 ph3.
  rewrite <- phUnion_assoc.
  rewrite phUnion_comm with ph1 ph2.
  by rewrite phUnion_assoc.
Qed.
Lemma phUnion_swap_r :
  forall ph1 ph2 ph3,
  phUnion (phUnion ph1 ph2) ph3 =
  phUnion (phUnion ph1 ph3) ph2.
Proof.
  intros ph1 ph2 ph3.
  rewrite phUnion_comm.
  rewrite phUnion_swap_l.
  by rewrite phUnion_assoc.
Qed.

Lemma phUnion_compat :
  forall ph1 ph2 ph3 ph4,
  phUnion (phUnion ph1 ph3) (phUnion ph2 ph4) =
  phUnion (phUnion ph1 ph2) (phUnion ph3 ph4).
Proof.
  intros ph1 ph2 ph3 ph4.
  rewrite phUnion_swap_l.
  repeat rewrite <- phUnion_assoc.
  by rewrite phUnion_comm with ph2 ph1.
Qed.

Lemma phUnion_update_free :
  forall ph1 ph2 phc l,
  ph2 l = PHCfree ->
  phUnion (phUpdate ph1 l phc) ph2 =
  phUpdate (phUnion ph1 ph2) l phc.
Proof.
  intros ph1 ph2 phc l H1.
  extensionality l'.
  unfold phUpdate, update, phUnion. desf.
  by rewrite H1, phcUnion_free_l.
Qed.


Lemma ghDisj_union_l :
  forall gh1 gh2 gh3,
  ghDisj gh1 gh2 ->
  ghDisj (ghUnion gh1 gh2) gh3 ->
  ghDisj gh2 gh3.
Proof.
  intros gh1 gh2 gh3 H1 H2 l.
  apply ghcDisj_union_l with (gh1 l); auto.
  by apply H2.
Qed.
Lemma ghDisj_union_r :
  forall gh1 gh2 gh3,
  ghDisj gh2 gh3 ->
  ghDisj gh1 (ghUnion gh2 gh3) ->
  ghDisj gh1 gh2.
Proof.
  intros gh1 gh2 gh3 H1 H2 l.
  apply ghcDisj_union_r with (gh3 l); auto.
  by apply H2.
Qed.

Lemma ghDisj_assoc_l :
  forall gh1 gh2 gh3,
  ghDisj gh1 gh2 ->
  ghDisj (ghUnion gh1 gh2) gh3 ->
  ghDisj gh1 (ghUnion gh2 gh3).
Proof.
  intros ???? H ?.
  apply ghcDisj_assoc_l. auto. apply H.
Qed.
Lemma ghDisj_assoc_r :
  forall gh1 gh2 gh3,
  ghDisj gh2 gh3 ->
  ghDisj gh1 (ghUnion gh2 gh3) ->
  ghDisj (ghUnion gh1 gh2) gh3.
Proof.
  intros ???? H ?.
  apply ghcDisj_assoc_r. auto. apply H.
Qed.

Lemma ghUnion_update :
  forall gh1 gh2 ghc1 ghc2 l,
  ghUpdate (ghUnion gh1 gh2) l (ghcUnion ghc1 ghc2) =
  ghUnion (ghUpdate gh1 l ghc1) (ghUpdate gh2 l ghc2).
Proof.
  ins. extensionality l'.
  unfold ghUnion, ghUpdate, update. desf.
Qed.

Lemma ghUnion_cell :
  forall gh1 gh2 l,
  ghcUnion (gh1 l) (gh2 l) = ghUnion gh1 gh2 l.
Proof. ins. Qed.

Lemma ghDisj_middle :
  forall gh1 gh2 gh3 gh4,
  ghDisj gh1 gh2 ->
  ghDisj gh3 gh4 ->
  ghDisj (ghUnion gh1 gh2) (ghUnion gh3 gh4) ->
  ghDisj gh2 gh3.
Proof.
  intros gh1 gh2 gh3 gh4 H1 H2 H3.
  apply ghDisj_union_l with gh1; auto.
  by apply ghDisj_union_r with gh4.
Qed.

Lemma ghDisj_compat :
  forall gh1 gh2 gh3 gh4,
  ghDisj gh1 gh3 ->
  ghDisj gh2 gh4 ->
  ghDisj (ghUnion gh1 gh3) (ghUnion gh2 gh4) ->
  ghDisj (ghUnion gh1 gh2) (ghUnion gh3 gh4).
Proof.
  intros gh1 gh2 gh3 gh4 H1 H2 H3.
  apply ghDisj_assoc_r.
  rewrite ghUnion_comm.
  apply ghDisj_assoc_l; auto.
  symmetry. by apply ghDisj_union_l in H3.
  rewrite ghUnion_comm.
  rewrite ghUnion_assoc.
  apply ghDisj_assoc_l; auto.
  by rewrite ghUnion_comm with gh4 gh2.
Qed.

Lemma ghUnion_swap_l :
  forall gh1 gh2 gh3,
  ghUnion gh1 (ghUnion gh2 gh3) =
  ghUnion gh2 (ghUnion gh1 gh3).
Proof.
  intros gh1 gh2 gh3.
  rewrite <- ghUnion_assoc.
  rewrite ghUnion_comm with gh1 gh2.
  by rewrite ghUnion_assoc.
Qed.
Lemma ghUnion_swap_r :
  forall gh1 gh2 gh3,
  ghUnion (ghUnion gh1 gh2) gh3 =
  ghUnion (ghUnion gh1 gh3) gh2.
Proof.
  intros gh1 gh2 gh3.
  rewrite ghUnion_comm.
  rewrite ghUnion_swap_l.
  by rewrite ghUnion_assoc.
Qed.

Lemma ghUnion_compat :
  forall gh1 gh2 gh3 gh4,
  ghUnion (ghUnion gh1 gh3) (ghUnion gh2 gh4) =
  ghUnion (ghUnion gh1 gh2) (ghUnion gh3 gh4).
Proof.
  intros gh1 gh2 gh3 gh4.
  rewrite ghUnion_swap_l.
  repeat rewrite <- ghUnion_assoc.
  by rewrite ghUnion_comm with gh2 gh1.
Qed.

Lemma ghUnion_update_free :
  forall gh1 gh2 ghc l,
  gh2 l = GHCfree ->
  ghUnion (ghUpdate gh1 l ghc) gh2 =
  ghUpdate (ghUnion gh1 gh2) l ghc.
Proof.
  intros gh1 gh2 ghc l H1.
  extensionality l'.
  unfold ghUpdate, update, ghUnion. desf.
  by rewrite H1, ghcUnion_free_l.
Qed.


(** *** Concretisation *)

(** The _concretisation_ of a permission heap [ph]
    is the heap that contains the concretisations
    of all heap cells of [ph]. *)

Definition phConcr (ph : PermHeap) : Heap :=
  fun l => phcConcr (ph l).

Lemma phConcr_update :
  forall ph l phc,
  phConcr (phUpdate ph l phc) =
  hUpdate (phConcr ph) l (phcConcr phc).
Proof.
  intros ph l phc. extensionality l'.
  unfold phConcr, phUpdate, hUpdate, update.
  desf.
Qed.

Lemma phConcr_disj_union_l :
  forall ph1 ph2 ph3,
  phDisj ph1 ph3 ->
  phDisj ph2 ph3 ->
  phConcr ph1 = phConcr ph2 ->
  phConcr (phUnion ph1 ph3) = phConcr (phUnion ph2 ph3).
Proof.
  intros ph1 ph2 ph3 H1 H2 H3.
  extensionality l. unfold phConcr.
  repeat rewrite <- phUnion_cell.
  apply phcConcr_disj_union_l; vauto.
  by apply equal_f with l in H3.
Qed.
Lemma phConcr_disj_union_r :
  forall ph1 ph2 ph3,
  phDisj ph1 ph3 ->
  phDisj ph2 ph3 ->
  phConcr ph1 = phConcr ph2 ->
  phConcr (phUnion ph3 ph1) = phConcr (phUnion ph3 ph2).
Proof.
  intros ph1 ph2 ph3 H1 H2 H3.
  rewrite phUnion_comm with ph3 ph1.
  rewrite phUnion_comm with ph3 ph2.
  apply phConcr_disj_union_l; auto.
Qed.


(** *** Snapshot *)

(** The _snapshot_ of any permission heap [ph] is the
    heap constructed from the snapshots of all [ph]s entries. *)

Definition phSnapshot (ph : PermHeap) : Heap :=
  fun l => phcSnapshot (ph l).

(** Several useful properties of permission heap snapshots: *)

Lemma phSnapshot_upd :
  forall ph l phc,
  phSnapshot (phUpdate ph l phc) =
  hUpdate (phSnapshot ph) l (phcSnapshot phc).
Proof.
  intros ph l phc. extensionality l'.
  unfold phSnapshot, phUpdate, hUpdate, update. desf.
Qed.

Lemma phSnapshot_disj_union_l :
  forall ph1 ph2 ph3,
  phDisj ph1 ph3 ->
  phDisj ph2 ph3 ->
  phSnapshot ph1 = phSnapshot ph2 ->
  phSnapshot (phUnion ph1 ph3) = phSnapshot (phUnion ph2 ph3).
Proof.
  intros ph1 ph2 ph3 H1 H2 H3.
  extensionality l. unfold phSnapshot.
  repeat rewrite <- phUnion_cell.
  apply phcSnapshot_disj_union_l; vauto.
  by apply equal_f with l in H3.
Qed.
Lemma phSnapshot_disj_union_r :
  forall ph1 ph2 ph3,
  phDisj ph1 ph3 ->
  phDisj ph2 ph3 ->
  phSnapshot ph1 = phSnapshot ph2 ->
  phSnapshot (phUnion ph3 ph1) = phSnapshot (phUnion ph3 ph2).
Proof.
  intros ph1 ph2 ph3 H1 H2 H3.
  rewrite phUnion_comm with ph3 ph1.
  rewrite phUnion_comm with ph3 ph2.
  apply phSnapshot_disj_union_l; auto.
Qed.


(** *** Finiteness *)

(** A permission heap is _finite_ if all mappings that are
    not free can be mapped to some finite structure,
    in this case a list. *)

Definition phFinite (ph : PermHeap) : Prop :=
  exists xs : list Val, forall l, ph l <> PHCfree -> In l xs.


Definition ghFinite (gh : GuardHeap) : Prop :=
  exists xs : list Guard, forall l, gh l <> GHCfree -> In l xs.

(** The main property of interest of finite permission heaps,
    is that one can always find a mapping that is free. *)

Lemma phFinite_free :
  forall ph,
  phFinite ph -> exists l, ph l = PHCfree.
Proof.
  intros ph (xs&FIN).
  assert (H : exists l, ~ In l xs) by apply val_inf.
  destruct H as (l&H).
  specialize FIN with l.
  exists l. tauto.
Qed.

(** Finiteness is preserved by any heap updates. *)

Lemma phFinite_update :
  forall ph l phc,
  phFinite ph -> phFinite (phUpdate ph l phc).
Proof.
  intros ph l phc (xs&FIN).
  assert (H1 : phc = PHCfree \/ ~ phc = PHCfree) by apply classic.
  destruct H1 as [H1|H1].
  (* [phc] is free *)
  - exists xs. intros l' H2. apply FIN.
    unfold phUpdate, update in H2. desf.
  (* [phc] is not free *)
  - exists (l :: xs). intros l' H2.
    specialize FIN with l'. simpls.
    unfold phUpdate, update in H2.
    destruct (val_eq_dec l l') as [|H3]; vauto.
    right. by apply FIN.
Qed.

(** The disjoint union of two finite permission heaps is finite. *)

Lemma phFinite_union :
  forall ph1 ph2,
  phFinite (phUnion ph1 ph2) <-> phFinite ph1 /\ phFinite ph2.
Proof.
  intros ph1 ph2. split.
  (* left-to-right *)
  - intros (xs & FIN).
    unfold phFinite. split.
    (* [ph1] is finite *)
    + exists xs. intros l H1.
      apply FIN. intro H2.
      apply phcUnion_not_free in H2; vauto.
    (* [ph2] is finite *)
    + exists xs. intros l H1.
      apply FIN. intro H2.
      apply phcUnion_not_free in H2; vauto.
  (* right-to-left *)
  - intro FIN.
    destruct FIN as ((xs1&FIN1)&(xs2&FIN2)).
    unfold phFinite.
    exists (xs1 ++ xs2). intros l H1.
    apply in_or_app.
    unfold phUnion in H1.
    apply phcUnion_not_free in H1.
    destruct H1 as [H1|H1].
    + left. by apply FIN1.
    + right. by apply FIN2.
Qed.

(** Permission heap concretisation preserves finiteness. *)

Lemma phFinite_concr :
  forall ph,
  phValid ph -> phFinite ph <-> hFinite (phConcr ph).
Proof.
  intros ph H1. split.
  (* left-to-right *)
  - intros (xs & FIN).
    exists xs. intros l H2. apply FIN.
    unfold phConcr, phcConcr in H2. desf.
  (* right-to-left *)
  - intros (xs&FIN).
    exists xs. intros l H2. apply FIN.
    unfold phValid in H1.
    specialize H1 with l.
    unfold phcValid in H1.
    unfold phConcr, phcConcr. desf.
Qed.


(** *** Heap cell conversion *)

(** This section discusses tools to convert the types
    of heap cells in permission heaps. *)

(** The operations [permheap_conv_std], [permheap_conv_proc],
    and [permheap_conv_act] are
    used to convert the heap cell at location [l] in a given
    permission heap [ph] to a _standard_,
    _process_, or _action_ heap cell, respectively.
    Later we define similar operations that work
    on sequences of heap locations. *)

Definition phConvStd (ph : PermHeap)(l : Val) : PermHeap :=
  phUpdate ph l (phcConvStd (ph l)).

Notation "'std' { ph ',' l }" := (phConvStd ph l).

(** Heap cell conversion is idempotent. *)

Lemma phConvStd_idemp :
  forall ph l, phConvStd (phConvStd ph l) l = phConvStd ph l.
Proof.
  intros ph l. extensionality l'.
  unfold phConvStd, phUpdate, update. desf.
  by apply phcConvStd_idemp.
Qed.

(** Heap cell conversion preserves validity. *)

Lemma phConvStd_valid :
  forall ph l,
  phValid ph <-> phValid (phConvStd ph l).
Proof.
  intros ph l. split; intros H l'.
  - unfold phValid in *.
    specialize H with l'.
    unfold phConvStd, phUpdate, update. desf.
    by rewrite <- phcConvStd_valid.
  - unfold phValid in *. specialize H with l'.
    unfold phConvStd, phUpdate, update in H.
    desf. by rewrite phcConvStd_valid.
Qed.

(** Heap cell conversion preserves disjointness. *)

Add Parametric Morphism : phConvStd
  with signature phDisj ==> eq ==> phDisj as phConvStd_disj.
Proof.
  intros ph1 ph2 H1 v. red. intro l.
  red in H1. red in H1. specialize H1 with l.
  unfold phConvStd, phUpdate, update. desf.
  by apply phcConvStd_disj.
Qed.

(** Heap cell conversion preserves entirety. *)

Lemma phConvStd_entire :
  forall ph l l',
  phcEntire (phConvStd ph l l') <-> phcEntire (ph l').
Proof.
  intros ph l l'. split; intro H.
  - unfold phConvStd, phUpdate, update in H. desf.
    by rewrite <- phcConvStd_entire.
  - unfold phConvStd, phUpdate, update. desf.
    by rewrite phcConvStd_entire.
Qed.

(** Heap cell conversion preserves concretisations. *)

Lemma phConvStd_concr :
  forall ph l,
  phConcr (phConvStd ph l) = phConcr ph.
Proof.
  intros ph l. extensionality l'.
  unfold phConcr, phConvStd, phUpdate, update. desf.
  by rewrite phcConvStd_concr.
Qed.

(** Heap cell conversion distributes over disjoint union. *)

Lemma phConvStd_union :
  forall ph1 ph2 l,
  phDisj ph1 ph2 ->
  phConvStd (phUnion ph1 ph2) l =
  phUnion (phConvStd ph1 l) (phConvStd ph2 l).
Proof.
  intros ph1 ph2 l H1.
  extensionality l'.
  red in H1. red in H1.
  specialize H1 with l'.
  unfold phUnion, phConvStd, phUpdate, update. desf.
  by apply phcConvStd_union.
Qed.

(** Free heap cells always convert to free heap cells. *)

Lemma phConvStd_free :
  forall ph l, ph l = PHCfree -> phConvStd ph l = ph.
Proof.
  intros ph l H. extensionality l'.
  unfold phConvStd, phUpdate, update. desf.
  rewrite H. by apply phcConvStd_free.
Qed.

Lemma phConvStd_free2 :
  forall ph l l',
  (phConvStd ph l) l' = PHCfree <-> ph l' = PHCfree.
Proof.
  intros ph l l'.
  unfold phConvStd, phUpdate, update. desf.
  by apply phcConvStd_free2.
Qed.

(** Any heap cell that is not converted stays the same. *)

Lemma phConvStd_pres :
  forall ph l l', l <> l' -> ph l' = phConvStd ph l l'.
Proof.
  intros ph l l' H1.
  unfold phConvStd, phUpdate, update. desf.
Qed.

(** Requesting any converted heap cell gives the converted heap cell. *)

Lemma phConvStd_apply :
  forall ph l, phConvStd ph l l = phcConvStd (ph l).
Proof. ins. unfold phConvStd, phUpdate, update. desf. Qed.

(** Below are various other useful properties of heap cell conversion. *)

Lemma phConvStd_disj_entire :
  forall ph1 ph2 l,
  phcEntire (ph1 l) -> phDisj ph1 ph2 -> phDisj (phConvStd ph1 l) ph2.
Proof.
  intros ph1 ph2 l H1 H2 l'.
  unfold phConvStd, phUpdate, update.
  desf. by apply phcConvStd_disj_entire.
Qed.

(** *** Heap cell batch conversions *)

(** The following operations are for converting a sequence
    (or set) of heap locations (i.e., for converting a
    batch or bulk of locations). *)

Fixpoint phConvStdMult (ph : PermHeap)(xs : list Val) : PermHeap :=
  match xs with
    | nil => ph
    | l :: xs' => phConvStd (phConvStdMult ph xs') l
  end.

Notation "'std' { ph ';' xs }" := (phConvStdMult ph xs).

(** Converting an empty batch of locations leaves the heap unchanged. *)

Lemma phConvStdMult_nil :
  forall ph, ph = phConvStdMult ph nil.
Proof. ins. Qed.

(** Properties related to converting a single heap cell: *)

Lemma phConvStdMult_single :
  forall ph l, phConvStd ph l = phConvStdMult ph [l].
Proof. ins. Qed.

(** Conversions of a non-empty batch of locations can be unfolded. *)

Lemma phConvStdMult_cons :
  forall xs l ph,
  phConvStdMult ph (l :: xs) = phConvStd (phConvStdMult ph xs) l.
Proof. ins. Qed.

(** Conversion of two batches of locations can be appended
    into a single batch. *)

Lemma phConvStdMult_app :
  forall xs ys ph,
  phConvStdMult ph (xs ++ ys) = phConvStdMult (phConvStdMult ph ys) xs.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ys ph. simpls. by rewrite IH.
Qed.

(** Batch conversions are closed under permutations. *)

Lemma phConvStdMult_permut :
  forall ph xs ys,
  Permutation xs ys -> phConvStdMult ph xs = phConvStdMult ph ys.
Proof.
  intros ph xs ys H. induction H; vauto.
  - simpl. by rewrite IHPermutation.
  - simpls. unfold phConvStd, phUpdate, update.
    extensionality l'. desf.
  - by rewrite IHPermutation1, IHPermutation2.
Qed.

Add Parametric Morphism : phConvStdMult
  with signature eq ==> @Permutation Val ==> eq
    as phConvStdMult_permut_mor.
Proof. ins. by apply phConvStdMult_permut. Qed.

(** Batch conversions are idempotent. *)

Lemma phConvStdMult_idemp :
  forall xs ph,
  phConvStdMult (phConvStdMult ph xs) xs = phConvStdMult ph xs.
Proof.
  induction xs as [|l' xs IH]; [done|].
  intros ph. rewrite <- phConvStdMult_app.
  assert (H1 : Permutation ((l' :: xs) ++ l' :: xs) (l' :: l' :: xs ++ xs)) by list_permutation.
  rewrite H1. simpl. rewrite phConvStd_idemp.
  by rewrite phConvStdMult_app, IH.
Qed.

(** Any duplicate conversions in a batch are subsumed. *)

Lemma phConvStdMult_subsume :
  forall xs l ph,
  In l xs -> phConvStdMult ph (l :: xs) = phConvStdMult ph xs.
Proof.
  induction xs as [|l' xs IH]; [done|].
  intros l ph H1. simpl in H1. destruct H1 as [H1|H1]; vauto.
  - simpls. by rewrite phConvStd_idemp.
  - rewrite perm_swap. simpls. rewrite IH; vauto.
Qed.

(** Batch conversions preserve heap validity. *)

Lemma phConvStdMult_valid :
  forall xs ph, phValid ph <-> phValid (phConvStdMult ph xs).
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph. split; intro H1.
  - simpl. apply phConvStd_valid. by rewrite <- IH.
  - simpl in H1. apply IH. by apply phConvStd_valid with l.
Qed.

(** Converting a batch of only free locations does not change the heap. *)

Lemma phConvStdMult_free :
  forall xs ph,
  (forall l, In l xs -> ph l = PHCfree) ->
  phConvStdMult ph xs = ph.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph H1. simpl.
  rewrite phConvStd_free.
  - apply IH. intros l' H2.
    apply H1. by apply in_cons.
  - rewrite IH.
    + apply H1. vauto.
    + intros l' H2. by apply H1, in_cons.
Qed.

Lemma phConvStdMult_free2 :
  forall xs ph l,
  phConvStdMult ph xs l = PHCfree <-> ph l = PHCfree.
Proof.
  induction xs as [|l' xs IH]; [done|].
  intros ph l. simpl. rewrite phConvStd_free2.
  by rewrite IH.
Qed.

(** Batch conversions preserve heap disjointness. *)

Lemma phConvStdMult_disj :
  forall xs ph1 ph2,
  phDisj ph1 ph2 -> phDisj (phConvStdMult ph1 xs) (phConvStdMult ph2 xs).
Proof.
  induction xs as [|x xs IH]; [done|].
  intros ph1 ph2 H1. simpl.
  apply phConvStd_disj; [|done]. by apply IH.
Qed.

Add Parametric Morphism : phConvStdMult
  with signature phDisj ==> @Permutation Val ==> phDisj
    as phConvStdMult_disj_mor.
Proof.
  intros ph1 ph2 H1 xs ys H2.
  rewrite H2. clear H2.
  by apply phConvStdMult_disj.
Qed.

(** Batch conversions preserve entirety. *)

Lemma phConvStdMult_entire:
  forall xs ph l,
  phcEntire (phConvStdMult ph xs l) <-> phcEntire (ph l).
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph l'. split; intro H.
  - simpl in H. rewrite <- IH.
    by rewrite <- phConvStd_entire with (l:=l).
  - simpl. rewrite phConvStd_entire with (l:=l).
    by rewrite IH.
Qed.

(** Batch conversions distribute over disjoint union. *)

Lemma phConvStdMult_union :
  forall xs ph1 ph2,
  phDisj ph1 ph2 ->
  phConvStdMult (phUnion ph1 ph2) xs =
  phUnion (phConvStdMult ph1 xs) (phConvStdMult ph2 xs).
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph1 ph2 H1. simpl.
  rewrite <- phConvStd_union.
  - by rewrite <- IH.
  - by apply phConvStdMult_disj.
Qed.

(** Batch conversions preserve heap concretisation. *)

Lemma phConvStdMult_concr :
  forall xs ph, phConcr (phConvStdMult ph xs) = phConcr ph.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph. simpl. by rewrite phConvStd_concr, IH.
Qed.

(** Any location that is not in the conversion batch
    is not affected by batch conversion. *)

Lemma phConvStdMult_pres :
  forall xs l ph, ~ In l xs -> ph l = phConvStdMult ph xs l.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros l' ph H1. simpl. rewrite IH.
  - apply phConvStd_pres. intro H2.
    apply H1. clarify. simpl. by left.
  - intro H2. apply H1. simpl. by right.
Qed.

(** Any location in the conversion batch is indeed converted. *)

Lemma phConvStdMult_apply :
  forall xs l ph,
  In l xs -> phConvStdMult ph xs l = phcConvStd (ph l).
Proof.
  induction xs as [|l' xs IH]; [done|].
  intros l ph H1. simpl in H1. destruct H1 as [H1|H1]; vauto.
  - simpl. rewrite phConvStd_apply.
    assert (H2 : In l xs \/ ~ In l xs) by apply classic.
    destruct H2 as [H2|H2]; vauto.
    + rewrite IH; auto. by apply phcConvStd_idemp.
    + by rewrite <- phConvStdMult_pres.
  - simpl. unfold phConvStd, phUpdate, update. desf.
    + rewrite IH; auto. by apply phcConvStd_idemp.
    + by apply IH.
Qed.

(** Below are various other useful properties of batch conversions. *)

Lemma phConvStdMult_disj_entire :
  forall xs ph1 ph2,
  (forall l, In l xs -> phcEntire (ph1 l)) ->
  phDisj ph1 ph2 ->
  phDisj (phConvStdMult ph1 xs) ph2.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph1 ph2 H1 H2. simpl.
  apply phConvStd_disj_entire.
  - rewrite phConvStdMult_entire. apply H1. vauto.
  - apply IH; auto. intros l' H3. apply H1. vauto.
Qed.

End Heaps.
