Require Import VST.floyd.proofauto.
(* Require Import Coq.Program.Equality. *)

Require Import my_tactics.
Require Import bst_spec.

(* bin_tree with *exactly* one hole *)
Inductive bin_tree_hole (A: Type) : Type :=
  | hole : bin_tree_hole A
  | node_hole_l : A -> bin_tree_hole A -> bin_tree A -> bin_tree_hole A
  | node_hole_r : A -> bin_tree A -> bin_tree_hole A -> bin_tree_hole A.
Arguments bin_tree_hole _%type_scope.
Arguments hole {A}%type_scope.
Arguments node_hole_l {A}%type_scope.
Arguments node_hole_r {A}%type_scope.

Fixpoint fill_hole {A} (outer: bin_tree_hole A) (inner: bin_tree A) : bin_tree A :=
  match outer with 
  | hole => inner
  | node_hole_l a l r => node a (fill_hole l inner) r
  | node_hole_r a l r => node a l (fill_hole r inner)
  end.

Fixpoint extend_hole {A} (outer inner: bin_tree_hole A) : bin_tree_hole A :=
  match outer with 
  | hole => inner
  | node_hole_l a l r => node_hole_l a (extend_hole l inner) r
  | node_hole_r a l r => node_hole_r a l (extend_hole r inner)
  end.

Definition bst_hole A := bin_tree_hole (Z * A).

(* This acts as a complement to search - where search returns the subtree, this returns the original tree,
   but with a hole where the subtree used to be. *)
Fixpoint search_make_hole {A} (k: Z) (b: bst A) : bst_hole A := 
  match b with 
  | leaf => hole
  | node (k', v) l r => 
      match k ?= k' with 
      | Eq => hole
      | Lt => node_hole_l (k', v) (search_make_hole k l) r
      | Gt => node_hole_r (k', v) l (search_make_hole k r)
      end 
  end.

Theorem fill_search_hole {A} : forall k (b: bst A),
  fill_hole (search_make_hole k b) (search k b) = b.
Proof.
  intros k b.
  induction b.
  - reflexivity.
  - simpl.
    destruct_pair.
    find_Z_compare_destruct; simpl.
    + reflexivity.
    + f_equal. assumption.
    + f_equal. assumption.
Qed.

(* This does search and search_make_hole together *)
Fixpoint split_bst_at {A} (k: Z) (b: bst A) : bst_hole A * bst A :=
  match b with 
  | leaf => (hole, leaf)
  | node (k', v) l r =>
      match k ?= k' with 
      | Eq => (hole, b)
      | Lt => let (outer, inner) := split_bst_at k l 
              in (node_hole_l (k', v) outer r, inner)
      | Gt => let (outer, inner) := split_bst_at k r 
              in (node_hole_r (k', v) l outer, inner)
      end 
  end.

(* Intended for when `search_path k outer inner` *)
Definition bst_subtract_path k (outer inner: bst Z) : bst_hole Z :=
  match inner with 
  | leaf => search_make_hole k outer
  | node (k',v) l r => search_make_hole k' outer 
  end.

Lemma bst_subtract_path_b_b : forall k b, bst_subtract_path k b b = hole.
Proof.
  intros.
  destruct b.
  - reflexivity.
  - simpl.
    destruct_pair.
    rewrite Z.compare_refl.
    reflexivity.
Qed.

Theorem fill_hole_bst_subtract_path: forall k b sub,
  well_ordered b ->
  search_path k b sub ->
  fill_hole (bst_subtract_path k b sub) sub = b.
Proof.
  intros k b sub H_wo H_path.
  induction H_path.
  - destruct b.
    + reflexivity.
    + simpl.
      destruct_pair.
      rewrite Z.compare_refl.
      reflexivity.
  - inversion H_wo; subst.
    simplify_assumps.
    destruct b.
    + simpl.
      rewrite Zaux.Zcompare_Lt by assumption.
      simpl.
      f_equal.
      simpl in *.
      assumption.
    + simpl.
      destruct_pair.
      simpl in *.
      apply search_path_is_subtree in H_path.
      find_Z_compare_destruct.
      * eapply subtree_forall in H_path; [|eassumption].
        inversion H_path; subst.
        simpl in *.
        lia.
      * simpl.
        f_equal.
        assumption.
      * eapply subtree_forall in H_path; [|eapply H4].
        inversion H_path; subst.
        simpl in *.
        lia.
  - inversion H_wo; subst.
    simplify_assumps.
    destruct b.
    + simpl.
      rewrite Zaux.Zcompare_Gt by lia.
      simpl.
      f_equal.
      simpl in *.
      assumption.
    + simpl.
      destruct_pair.
      simpl in *.
      apply search_path_is_subtree in H_path.
      find_Z_compare_destruct.
      * eapply subtree_forall in H_path; [|eassumption].
        inversion H_path; subst.
        simpl in *.
        lia.
      * eapply subtree_forall in H_path; [|eapply H5].
        inversion H_path; subst.
        simpl in *.
        lia.
      * simpl.
        f_equal.
        assumption.
Qed.
