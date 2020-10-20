Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

(* CompCert-generated representation of bst.c *)
Require Import bst.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* Required for `dependent induction` tactic *)
Require Import Coq.Program.Equality.

(* Some custom tactics *)
Require Import my_tactics.

(* BST specification *)

Inductive bin_tree (A: Type) : Type := 
  | leaf : bin_tree A
  | node : A -> bin_tree A -> bin_tree A -> bin_tree A.
Arguments bin_tree _%type_scope.
Arguments leaf {A}%type_scope.
Arguments node {A}%type_scope.

Inductive bin_tree_forall {A} : bin_tree A -> (A -> Prop) -> Prop :=
  | bin_tree_forall_leaf : forall p, bin_tree_forall leaf p 
  | bin_tree_forall_node : forall (p: A -> Prop) a l r,
      p a -> bin_tree_forall l p -> bin_tree_forall r p -> bin_tree_forall (node a l r) p.

Inductive well_ordered {A} : bin_tree (Z * A) -> Prop :=
  | well_ordered_leaf : well_ordered leaf 
  | well_ordered_node : forall k v l r,
      bin_tree_forall l (fun n => fst n < k) -> 
      bin_tree_forall r (fun n => fst n > k) -> 
      well_ordered l ->
      well_ordered r ->
      well_ordered (node (k, v) l r).

Definition bst A := bin_tree (Z * A).
(* Definition bst A := sig well_ordered. *)
Definition bst_wo A := {b : bst A | well_ordered b}.

Inductive is_subtree {A} : bin_tree A -> bin_tree A -> Prop :=
  | is_subtree_refl  : forall b, is_subtree b b 
  | is_subtree_left  : forall b n l r, is_subtree b l -> is_subtree b (node n l r)
  | is_subtree_right : forall b n l r, is_subtree b r -> is_subtree b (node n l r).

Lemma is_subtree_leaf : forall {A} (b: bin_tree A), is_subtree leaf b.
Proof.
  intros A b.
  induction b; constructor; assumption.
Qed.

Theorem subtree_forall : forall {A} sub b (p: A -> Prop),
  is_subtree sub b -> bin_tree_forall b p -> bin_tree_forall sub p.
Proof.
  intros.
  induction H;
  try (apply IHis_subtree; inversion H0);
  assumption.
Qed.

Theorem subtree_well_ordered : forall {A} (b sub: bst A),
  is_subtree sub b -> well_ordered b -> well_ordered sub.
Proof.
  intros.
  induction b.
  - destruct sub.
    + constructor.
    + inversion H.
  - inversion H; subst.
    + assumption.
    + inversion H0; apply IHb1; assumption.
    + inversion H0; apply IHb2; assumption.
Qed.

Fixpoint insert {A} (k: Z) (v: A) (b: bst A) : bst A :=
  match b with 
  | leaf => node (k, v) leaf leaf
  | node (k', v') l r => 
      match k ?= k' with 
      | Eq => node (k', v) l r 
      | Lt => node (k', v') (insert k v l) r 
      | Gt => node (k', v') l (insert k v r)
      end 
  end.

Lemma insert_forall {A} : forall (p: (Z * A) -> Prop) k v bst,
  p (k, v) -> bin_tree_forall bst p -> bin_tree_forall (insert k v bst) p.
Proof.
  intros p k v b H.
  induction b; intro H0; simpl.
  - constructor; assumption.
  - destruct_pair. find_Z_compare_destruct;
    inversion H0; subst; constructor; 
    try (apply IHb1 + apply IHb2); 
    assumption.
Qed.

Theorem insert_well_ordered {A}: forall (b: bst A) k v, 
  well_ordered b -> well_ordered (insert k v b).
Proof.
  intro b; induction b; intros k v H; simpl.
  - repeat constructor.
  - inversion H; subst.
    find_Z_compare_destruct;
    constructor; try (apply insert_forall + apply IHb1 + apply IHb2); assumption.
Qed.

Definition insert_wo {A} (k: Z) (v: A) (b: bst_wo A) : bst_wo A.
  refine (match b with 
  | exist bt _ => exist _ (insert k v bt) _
  end).
  apply insert_well_ordered; assumption.
Defined.

Fixpoint search {A} (k: Z) (b: bst A) : bst A := 
  match b with 
  | leaf => leaf
  | node (k', v) l r => 
      match k ?= k' with 
      | Eq => b
      | Lt => search k l
      | Gt => search k r
      end 
  end.

Theorem search_is_subtree : forall {A} k (b sub: bst A),
  search k b = sub -> is_subtree sub b.
Proof.
  intros A k b sub.
  induction b; try destruct_pair; simpl; intro H.
  - subst. constructor.
  - find_Z_compare_destruct.
    + subst. constructor.
    + apply is_subtree_left.
      apply IHb1.
      assumption.
    + apply is_subtree_right.
      apply IHb2.
      assumption.
Qed.

Lemma search_well_ordered : forall {A} k (b sub: bst A),
  search k b = sub -> well_ordered b -> well_ordered sub.
Proof.
  intros.
  eapply subtree_well_ordered.
  eapply search_is_subtree.
  eassumption.
  assumption.
Qed.

Theorem search_insert {A}: forall k v (b: bst A),
  exists l r, search k (insert k v b) = node (k, v) l r.
Proof.
  intros k v b.
  induction b.
  - simpl.
    rewrite Z.compare_refl.
    unify_goal.
  - simpl. destruct_pair.
    find_Z_compare_destruct;
    subst; simpl; rewrite Heqc; assumption + unify_goal.
Qed.

(* BST representations *)

Definition t_bst := Tstruct _bst noattr.

Fixpoint bst_rep (b: bst Z) (p: val): mpred :=
  match b with 
  | leaf => (!! (p = nullval)) && emp 
  | node (k, v) l r =>
      EX pl pr: val, 
        malloc_token Ews t_bst p *
        data_at Ews t_bst (Vint (Int.repr k), (Vint (Int.repr v), (pl, pr))) p *
        bst_rep l pl *
        bst_rep r pr
  end.

(* For now, this is given axiomatically *)
Definition val_eq (x y : val) : bool. Admitted.
Theorem reflect_val_eq : forall x y, reflect (x = y) (val_eq x y). Admitted.
Theorem val_eq_reflexive : forall x, val_eq x x = true. Admitted.

Fixpoint bst_rep_w_filter (small: bst Z) (psmall: val) (big: bst Z) (pbig: val) :=
  if val_eq psmall pbig then 
    !! (psmall = pbig /\ small = big) && emp
  else match big with 
  | leaf => (!! (pbig = nullval)) && emp 
  | node (k, v) l r =>
      EX pl pr: val, 
        malloc_token Ews t_bst pbig *
        data_at Ews t_bst (Vint (Int.repr k), (Vint (Int.repr v), (pl, pr))) pbig *
        bst_rep l pl *
        bst_rep r pr
  end.

Definition bst_rep_and_context (small: bst Z) (psmall: val) (big: bst Z) (pbig: val) :=
  sepcon (bst_rep small psmall) (bst_rep_w_filter small psmall big pbig).

(* Suggested by VC. Idea is that the representation of bst shouldn't typically be dealt with explicitly *)
Arguments bst_rep b p : simpl never.
Arguments bst_rep_w_filter small psmall big pbig : simpl never.
Arguments bst_rep_and_context small psmall big pbig : simpl never.

Lemma bst_rep_local_prop: forall b p,
  bst_rep b p |-- !! (is_pointer_or_null p /\ (p = nullval <-> b = leaf)).
Proof.
  intros b p. induction b; unfold bst_rep.
  - entailer!. tauto.
  - destruct a.
    fold bst_rep.
    entailer.
    entailer!.
    split.
    + intro; subst.
      eapply field_compatible_nullval. eassumption.
    + discriminate.
Qed.
Hint Resolve bst_rep_local_prop : saturate_local.

Lemma bst_rep_valid_pointer: forall b p,
  bst_rep b p |-- valid_pointer p.
Proof. 
  intros b p. induction b; unfold bst_rep; try destruct a; entailer. 
Qed.
Hint Resolve bst_rep_valid_pointer : valid_pointer. 

(* Function specifications *) 

Definition new_bst_spec: ident * funspec := DECLARE _new_bst
  WITH k: Z, v: Z, gv: globals
  PRE [tint, tint]
    PROP (repable_signed k; repable_signed v)
    PARAMS (Vint (Int.repr k); Vint (Int.repr v)) GLOBALS (gv)
    SEP (mem_mgr gv)
  POST [tptr t_bst] 
    EX p: val,
      PROP ()
      RETURN (p)
      SEP (bst_rep (node (k, v) leaf leaf) p; mem_mgr gv).

Definition insert_bst_spec: ident * funspec :=
  DECLARE _insert_bst
  WITH bst_ptr: val, head: val, k: Z, v: Z, b: bst Z, gv: globals
  PRE [tptr (tptr t_bst), tint, tint]
    PROP (repable_signed k; repable_signed v;
          bin_tree_forall b (fun n => repable_signed (fst n)))
    PARAMS (bst_ptr; Vint (Int.repr k); Vint (Int.repr v)) GLOBALS (gv)
    SEP (data_at Ews (tptr t_bst) head bst_ptr;
         bst_rep b head;
         mem_mgr gv)
  POST [tvoid]
    EX new_bst: val,
      PROP ()
      RETURN ()
      SEP (data_at Ews (tptr t_bst) new_bst bst_ptr; 
           bst_rep (insert k v b) new_bst;
           mem_mgr gv).

Definition search_bst_spec: ident * funspec := 
  DECLARE _search_bst 
  WITH head: val, k: Z, b: bst Z, gv: globals 
  PRE [tptr t_bst, tint]
    PROP (repable_signed k; bin_tree_forall b (fun n => repable_signed (fst n)))
    PARAMS (head; Vint (Int.repr k)) GLOBALS (gv)
    SEP (bst_rep b head; mem_mgr gv)
  POST [tptr t_bst] 
    EX vret, 
      PROP () 
      RETURN (vret) 
      SEP (bst_rep_and_context (search k b) vret b head; mem_mgr gv).

Definition Gprog: funspecs := 
  ltac:(with_library prog [new_bst_spec; insert_bst_spec; search_bst_spec]).

(* Proofs of C functions *)

(* But first, some definitions for the invariants *)

(* The direction of transitivity here is nice for induction, but doesn't correspond 
   to the intuitive direction in which a path grows. *)
Inductive search_path : Z -> bst Z -> bst Z -> Prop := 
  | path_refl : forall k b, search_path k b b
  | path_step_l : forall k k' v l r b,
      search_path k l b -> k < k' -> search_path k (node (k',v) l r) b
  | path_step_r : forall k k' v l r b,
      search_path k r b -> k > k' -> search_path k (node (k',v) l r) b.

(* This is the direction a path will actually grow in *)
Lemma path_step_down_l : forall k head k' v l r,
  search_path k head (node (k',v) l r) -> k < k' -> search_path k head l.
Proof.
  intros. dependent induction H.
  - apply path_step_l.
    + constructor. 
    + assumption.
  - apply path_step_l.
    + eapply IHsearch_path; trivial.
    + assumption. 
  - apply path_step_r.
    + eapply IHsearch_path; trivial.
    + assumption.
Qed.
Lemma path_step_down_r : forall k head k' v l r,
  search_path k head (node (k',v) l r) -> k > k' -> search_path k head r.
Proof.
  intros. dependent induction H.
  - apply path_step_r.
    + constructor. 
    + assumption.
  - apply path_step_l.
    + eapply IHsearch_path; trivial.
    + assumption. 
  - apply path_step_r.
    + eapply IHsearch_path; trivial.
    + assumption.
Qed.

Theorem search_path_fail : forall k b, search_path k b leaf -> search k b = leaf.
Proof.
  intros. dependent induction H.
  - reflexivity.
  - simpl.
    rewrite Zaux.Zcompare_Lt by assumption.
    apply IHsearch_path.
    reflexivity.
  - simpl.
    rewrite Zaux.Zcompare_Gt by lia.
    apply IHsearch_path.
    reflexivity.
Qed.

Theorem search_path_success: forall k b v l r,
  search_path k b (node (k,v) l r) -> search k b = (node (k,v) l r).
Proof.
  intros. dependent induction H.
  - simpl.
    rewrite Z.compare_refl.
    reflexivity.
  - simpl.
    rewrite Zaux.Zcompare_Lt by assumption. 
    apply IHsearch_path.
    reflexivity.
  - simpl.
    rewrite Zaux.Zcompare_Gt by lia.
    apply IHsearch_path.
    reflexivity.
Qed.

Lemma search_path_constant : forall k b1 b2,
  search_path k b1 b2 -> search k b1 = search k b2.
Proof.
  intros k b1 b2 H.
  dependent induction H; simpl.
  - reflexivity.
  - rewrite Zaux.Zcompare_Lt; assumption.
  - rewrite Zaux.Zcompare_Gt by lia. assumption.
Qed.

Theorem search_path_is_subtree: forall k b sub, search_path k b sub -> is_subtree sub b.
Proof.
  intros.
  induction H.
  - constructor.
  - apply is_subtree_left. assumption.
  - apply is_subtree_right. assumption.
Qed.

Theorem body_search_bst: semax_body Vprog Gprog f_search_bst search_bst_spec.
Proof.
  start_function.
  forward_loop (
    EX curr: val, EX curr_b: bst Z,
      PROP (search_path k b curr_b)
      LOCAL (
        gvars gv; temp _bst__1 curr;
        temp _key (Vint (Int.repr k)))
      SEP (bst_rep_and_context curr_b curr b head; mem_mgr gv)
  ).
  { repeat EExists.
    entailer!.
    - constructor.
    - destruct b; simplify_assumps; subst;
      expand bst_rep_and_context; expand bst_rep_w_filter; expand bst_rep.
      + rewrite val_eq_reflexive. entailer!.
      + repeat destruct_pair. 
        Intros pl pr.
        repeat EExists.
        rewrite val_eq_reflexive.
        entailer!. }
  Intros curr curr_b.
  forward_if.
  { destruct curr_b; expand bst_rep_and_context; entailer!. }
  { forward.
    EExists.
    entailer!.
    expand bst_rep_and_context.
    entailer!.
    simplify_assumps; subst.
    rewrite search_path_fail by assumption.
    entailer!. }
  assert_PROP (curr_b <> leaf) by (expand bst_rep_and_context; entailer!; find_contradiction).
  destruct curr_b; [contradiction|].
  expand bst_rep_and_context.
  expand bst_rep.
  destruct_pair.
  Intros pl pr.
  forward.
  forward_if.
  { forward.
    EExists.
    entailer!.
    erewrite search_path_constant by eassumption.
    assert (k = z).
    { apply repr_inj_signed; try assumption.
      apply search_path_is_subtree in H1.
      pose proof (subtree_forall _ _ _ H1 H0) as H10.
      inversion H10; simpl in *; assumption. }
    subst. simpl.
    rewrite Z.compare_refl.
    expand bst_rep_and_context.
    entailer!.
    expand bst_rep.
    repeat EExists.
    entailer!. }
  forward.
  forward_if.
  - forward.
    Exists pl curr_b1.
    entailer!.
    + eapply path_step_down_l; [eassumption|].
      rewrite Int.signed_repr in H5. assumption.
      apply search_path_is_subtree in H1.
      pose proof (subtree_forall _ _ _ H1 H0) as H11.
      inversion H11; simpl in *; assumption.
    + expand bst_rep_and_context.
      entailer!.
      (* This looks tough, but correct. *)
      expand bst_rep_w_filter.
      (* Note that curr_b is a subtree of b. When they are equal, so are curr/head *)
      (* destruct (reflect_val_eq curr head).
      * entailer!. *)
      admit.
  - forward.
    Exists pr curr_b2.
    entailer!.
    + eapply path_step_down_r; [eassumption|].
      apply search_path_is_subtree in H1.
      pose proof (subtree_forall _ _ _ H1 H0) as H11.
      rewrite Int.signed_repr in H5.
      * enough (k <> z). lia.
        apply repr_inj_signed'; try assumption.
        inversion H11; simpl in *; assumption.
      * inversion H11; simpl in *; assumption.
    + admit.
Admitted.