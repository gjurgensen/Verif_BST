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
Definition bst_hole A := bin_tree_hole (Z * A).

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

Lemma wo_node_eq {A} : forall k (v1 v2: A) l1 l2 r1 r2,
  well_ordered (node (k,v1) l1 r1) ->
  is_subtree (node (k,v2) l2 r2) (node (k,v1) l1 r1) ->
  node (k,v1) l1 r1 = node (k,v2) l2 r2.
Proof.
  intros.
  inversion H0; subst.
  - reflexivity. 
  - inversion H; subst. 
    eapply subtree_forall in H3; [|eassumption].
    inversion H3; subst.
    simpl in H5. lia.
  - inversion H; subst. 
    eapply subtree_forall in H3; [|eassumption].
    inversion H3; subst.
    simpl in H5. lia.
Qed.

Lemma wo_subtree_left {A} : forall k1 k2 (v1 v2: A) l1 l2 r1 r2,
  well_ordered (node (k1,v1) l1 r1) ->
  is_subtree (node (k2,v2) l2 r2) (node (k1,v1) l1 r1) ->
  k2 < k1 ->
  is_subtree (node (k2,v2) l2 r2) l1.
Proof.
  intros.
  inversion H0; subst.
  - lia.
  - assumption.
  - inversion H; subst.
    eapply subtree_forall in H4; [|eassumption].
    inversion H4; subst.
    simpl in H6. lia.
Qed.

Lemma wo_subtree_right {A} : forall k1 k2 (v1 v2: A) l1 l2 r1 r2,
  well_ordered (node (k1,v1) l1 r1) ->
  is_subtree (node (k2,v2) l2 r2) (node (k1,v1) l1 r1) ->
  k2 > k1 ->
  is_subtree (node (k2,v2) l2 r2) r1.
Proof.
  intros.
  inversion H0; subst.
  - lia.
  - inversion H; subst.
    eapply subtree_forall in H4; [|eassumption].
    inversion H4; subst.
    simpl in H6. lia.
  - assumption.
Qed.

Theorem search_spec {A} : forall (b: bst A) k v l r,
  well_ordered b ->
  is_subtree (node (k,v) l r) b ->
  search k b = node (k,v) l r.
Proof.
  intros.
  induction b.
  - inversion H0.
  - inversion H; subst.
    simplify_assumps.
    simpl.
    find_Z_compare_destruct.
    + eapply wo_node_eq; assumption.
    + apply IHb1.
      eapply wo_subtree_left; eassumption.
    + apply IHb2.
      eapply wo_subtree_right; eassumption.
Qed.

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

Theorem search_is_subtree : forall {A} k (b sub: bst A),
  search k b = sub -> is_subtree sub b.
Proof.
  intros A k b sub.
  induction b; try destruct_pair; simpl; intro H.
  - subst. constructor.
  - find_Z_compare_destruct.
    + constructor.
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
    simpl; rewrite Heqc; assumption + unify_goal.
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

Theorem generalize_node_rep : forall (p pl pr: val) k v l r,
  (malloc_token Ews t_bst p *
  data_at Ews t_bst (Vint (Int.repr k), (Vint (Int.repr v), (pl, pr))) p *
  bst_rep l pl *
  bst_rep r pr
  |-- bst_rep (node (k,v) l r) p
  )%logic.
Proof.
  intros.
  expand bst_rep.
  repeat EExists.
  entailer!.
Qed.

Fixpoint bst_hole_rep (b: bst_hole Z) (p: val): mpred :=
  match b with 
  | hole => emp
  | node_hole_l (k, v) l r =>
      EX pl pr: val,
        malloc_token Ews t_bst p *
        data_at Ews t_bst (Vint (Int.repr k), (Vint (Int.repr v), (pl, pr))) p *
        bst_hole_rep l pl *
        bst_rep r pr
  | node_hole_r (k, v) l r =>
      EX pl pr: val,
        malloc_token Ews t_bst p *
        data_at Ews t_bst (Vint (Int.repr k), (Vint (Int.repr v), (pl, pr))) p *
        bst_rep l pl *
        bst_hole_rep r pr
  end.

(* Definition bst_rep_w_ptr b head k sub := 
  let (outer, inner) := split_bst_at k b
  in (bst_hole_rep outer head * bst_rep inner sub)%logic. *)

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
          bin_tree_forall b (fun n => repable_signed (fst n));
          well_ordered b)
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
    PROP (repable_signed k;
          bin_tree_forall b (fun n => repable_signed (fst n));
          well_ordered b)
    PARAMS (head; Vint (Int.repr k)) GLOBALS (gv)
    SEP (bst_rep b head; mem_mgr gv)
  POST [tptr t_bst] 
    EX vret,
      (* PROP (fill_hole (search k b) outer_b = b) *)
      PROP ()
      RETURN (vret)
      SEP (bst_hole_rep (search_make_hole k b) head; bst_rep (search k b) vret; mem_mgr gv).
 
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

(* Definition search_path_rep (k: Z) (outer inner: bst Z) : mpred :=
  !! (search_path k outer inner) && () *)

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

(* Theorem search_path_fail_hole : forall k b,
  search_path k b leaf -> search_make_hole k b = b.
Proof.
  intros k b H.
  induction b.
  - reflexivity.
  - simpl.
    destruct_pair.
    find_Z_compare_destruct.
    + find_contradiction.
    + f_equal.
      apply IHb1.
      inversion H; subst.
      * assumption.
      * lia.
    + f_equal.
      apply IHb2.
      inversion H; subst.
      * lia.
      * assumption.
Qed.
 *)

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

Definition proper_subtree {A} (b1 b2: bin_tree A) := b1 <> b2 /\ is_subtree b1 b2.

Ltac break_let :=
  match goal with
    | [ H : context [ (let (_,_) := ?X in _) ] |- _ ] => destruct X eqn:?
    | [ |- context [ (let (_,_) := ?X in _) ] ] => destruct X eqn:?
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
    break_let.
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

Theorem is_subtree_up_left {A}: forall (a: A) l r b,
  is_subtree (node a l r) b -> is_subtree l b.
Proof.
  intros.
  dependent induction H.
  - apply is_subtree_left. constructor.
  - apply is_subtree_left.
    eapply IHis_subtree.
    reflexivity.
  - apply is_subtree_right.
    eapply IHis_subtree.
    reflexivity.
Qed.

Theorem is_subtree_up_right {A}: forall (a: A) l r b,
  is_subtree (node a l r) b -> is_subtree r b.
Proof.
  intros.
  dependent induction H.
  - apply is_subtree_right. constructor.
  - apply is_subtree_left.
    eapply IHis_subtree.
    reflexivity.
  - apply is_subtree_right.
    eapply IHis_subtree.
    reflexivity.
Qed.

(* Alternatively, base this on a "proper" search_path *)
(* Theorem hole_rep_fuse_left2 : forall search_k k v l r k' v' l' r' (curr head pl pr: val),
  well_ordered (node (k,v) l r) ->
  search_path search_k (node (k,v) l r) (node (k',v') l' r') ->
  search_k < k' ->
  (node (k,v) l r = node (k',v') l' r' -> head = curr) ->
    bst_hole_rep (bst_subtract_path k (node (k,v) l r) (node (k',v') l' r')) head *
    malloc_token Ews t_bst curr *
    data_at Ews t_bst (Vint (Int.repr k'), (Vint (Int.repr v'), (pl, pr))) curr *
    bst_rep r' pr
    |-- bst_hole_rep (bst_subtract_path search_k (node (k,v) l r) l') head.
Proof.
  intros search_k k v l r.
  induction (node (k,v) l r).
  - intros. inversion H0.
  -
    intros.
    simpl.
    destruct_pair.
    find_Z_compare_destruct.
    + apply search_path_is_subtree in H0.
      apply wo_node_eq in H0; [|assumption].
      inversion H0; subst.
      simplify_assumps; subst.
      simpl; cancel.
      destruct l'.
      * simpl.
        rewrite Zaux.Zcompare_Lt by assumption.
        simpl.
        repeat EExists.
        entailer!.
      * simpl. 
        destruct_pair.
        rewrite Z.compare_refl.
        rewrite Zaux.Zcompare_Lt.
        -- simpl.
           Exists pl pr.
           entailer!.
        -- inversion H; subst.
           inversion H5; subst.
           simpl in *; assumption.
    + simpl in *.
      Intros pl_head pr_head.
      Check (IHb1 z z0 b1 b2 head pl_head pl_head pr_head).
      sep_apply (IHb1 k' v' l' r' curr pl_head pl pr).
      sep_apply IHb1.

      destruct l'.
      *  *)

 
Theorem hole_rep_fuse_left : forall b k curr_k v l r (curr head pl pr: val),
  well_ordered b ->
  search_path k b (node (curr_k, v) l r) ->
  k < curr_k ->
  (node (curr_k, v) l r = b -> curr = head) ->
    bst_hole_rep (bst_subtract_path k b (node (curr_k, v) l r)) head *
    malloc_token Ews t_bst curr *
    data_at Ews t_bst (Vint (Int.repr curr_k), (Vint (Int.repr v), (pl, pr))) curr *
    bst_rep r pr
    |-- bst_hole_rep (bst_subtract_path k b l) head.
Proof.
  intros.
  generalize dependent head.
  induction b; intros.
  - inversion H0.
  - simpl. destruct_pair.
    find_Z_compare_destruct.
    + apply search_path_is_subtree in H0.
      apply wo_node_eq in H0; [|assumption].
      inversion H0; subst; clear H0.
      simplify_assumps; subst.
      destruct l.
      * simpl.
        rewrite Zaux.Zcompare_Lt by assumption.
        simpl.
        Exists pl pr.
        entailer!.
      * simpl.
        destruct_pair. 
        rewrite Z.compare_refl.
        rewrite Zaux.Zcompare_Lt.
        -- simpl.
           Exists pl pr.
           entailer!.
        -- inversion H; subst.
           inversion H5; subst.
           simpl in *; assumption.
    + simpl in *.
      Intros head_pl head_pr.
      sep_apply IHb1.
      * inversion H. assumption.
      * inversion H0; subst.
        -- lia.
        -- assumption.
        -- apply search_path_is_subtree in H10.
           inversion H; subst.
           eapply subtree_forall in H10; [|eapply H9].
           inversion H10; subst.
           simpl in *.
           lia.
      * admit.
      * destruct l.
        -- simpl. 
           rewrite Zaux.Zcompare_Lt.
           ++ simpl.
              Exists head_pl head_pr.
              entailer!.
           ++ inversion H0; subst.
              ** lia.
              ** assumption.
              ** apply search_path_is_subtree in H10.
                 inversion H; subst.
                 eapply subtree_forall in H10; [|eassumption].
                 inversion H10; subst.
                 simpl in *.
                 lia.
        -- simpl.
           destruct_pair.
           rewrite Zaux.Zcompare_Lt.
           ++ simpl.
              Exists head_pl head_pr.
              entailer!.
           ++ apply search_path_is_subtree in H0.
              apply wo_subtree_left in H0; try assumption.
              apply is_subtree_up_left in H0.
              inversion H; subst.
              eapply subtree_forall in H0; [|eassumption].
              inversion H0; subst.
              simpl in *; assumption.
    + simpl in *.
      Intros head_pl head_pr.
      sep_apply IHb2.
      * inversion H. assumption.
      * inversion H0; subst.
        -- lia.
        -- apply search_path_is_subtree in H10.
           inversion H; subst.
           eapply subtree_forall in H10; [|eassumption].
           inversion H10; subst.
           simpl in *.
           lia.
        -- assumption.
      * admit.
      * destruct l.
        -- simpl. 
           rewrite Zaux.Zcompare_Gt.
           ++ simpl.
              Exists head_pl head_pr.
              entailer!.
           ++ inversion H0; subst.
              ** lia.
              ** apply search_path_is_subtree in H10.
                 inversion H; subst.
                 eapply subtree_forall in H10; [|eassumption].
                 inversion H10; subst.
                 simpl in *.
                 lia.
              ** lia.
        -- simpl.
           destruct_pair.
           rewrite Zaux.Zcompare_Gt.
           ++ simpl.
              Exists head_pl head_pr.
              entailer!.
           ++ apply search_path_is_subtree in H0.
              apply wo_subtree_right in H0; try assumption.
              apply is_subtree_up_left in H0.
              inversion H; subst.
              eapply subtree_forall in H0; [|eassumption].
              inversion H0; subst.
              simpl in *; lia.
Admitted.

Theorem hole_rep_fuse_right : forall b k curr_k v l r (curr head pl pr: val),
  well_ordered b ->
  search_path k b (node (curr_k, v) l r) ->
  k > curr_k ->
  (node (curr_k, v) l r = b -> curr = head) ->
    bst_hole_rep (bst_subtract_path k b (node (curr_k, v) l r)) head *
    malloc_token Ews t_bst curr *
    data_at Ews t_bst (Vint (Int.repr curr_k), (Vint (Int.repr v), (pl, pr))) curr *
    bst_rep l pl
    |-- bst_hole_rep (bst_subtract_path k b r) head.
Proof.
  intros.
  generalize dependent head.
  induction b; intros.
  - inversion H0.
  - simpl. destruct_pair.
    find_Z_compare_destruct.
    + apply search_path_is_subtree in H0.
      apply wo_node_eq in H0; [|assumption].
      inversion H0; subst; clear H0.
      simplify_assumps; subst.
      destruct r.
      * simpl.
        rewrite Zaux.Zcompare_Gt by lia.
        simpl.
        Exists pl pr.
        entailer!.
      * simpl.
        destruct_pair. 
        rewrite Z.compare_refl.
        rewrite Zaux.Zcompare_Gt.
        -- simpl.
           Exists pl pr.
           entailer!.
        -- inversion H; subst.
           inversion H6; subst.
           simpl in *; lia.
    + simpl in *.
      Intros head_pl head_pr.
      sep_apply IHb1.
      * inversion H. assumption.
      * inversion H0; subst.
        -- lia.
        -- assumption.
        -- apply search_path_is_subtree in H10.
           inversion H; subst.
           eapply subtree_forall in H10; [|eapply H9].
           inversion H10; subst.
           simpl in *.
           lia.
      * admit.
      * destruct r.
        -- simpl. 
           rewrite Zaux.Zcompare_Lt.
           ++ simpl.
              Exists head_pl head_pr.
              entailer!.
           ++ inversion H0; subst.
              ** lia.
              ** assumption.
              ** apply search_path_is_subtree in H10.
                 inversion H; subst.
                 eapply subtree_forall in H10; [|eassumption].
                 inversion H10; subst.
                 simpl in *.
                 lia.
        -- simpl.
           destruct_pair.
           rewrite Zaux.Zcompare_Lt.
           ++ simpl.
              Exists head_pl head_pr.
              entailer!.
           ++ 
              (* Show that node_z1 is a subtree of b1 *)
              apply search_path_is_subtree in H0.
              apply wo_subtree_left in H0; try assumption.
              apply is_subtree_up_right in H0.
              inversion H; subst.
              eapply subtree_forall in H0; [|eassumption].
              inversion H0; subst.
              simpl in *; assumption.
    + simpl in *.
      Intros head_pl head_pr.
      sep_apply IHb2.
      * inversion H. assumption.
      * inversion H0; subst.
        -- lia.
        -- apply search_path_is_subtree in H10.
           inversion H; subst.
           eapply subtree_forall in H10; [|eassumption].
           inversion H10; subst.
           simpl in *.
           lia.
        -- assumption.
      * admit.
      * destruct r.
        -- simpl. 
           rewrite Zaux.Zcompare_Gt.
           ++ simpl.
              Exists head_pl head_pr.
              entailer!.
           ++ inversion H0; subst.
              ** lia.
              ** apply search_path_is_subtree in H10.
                 inversion H; subst.
                 eapply subtree_forall in H10; [|eassumption].
                 inversion H10; subst.
                 simpl in *.
                 lia.
              ** lia.
        -- simpl.
           destruct_pair.
           rewrite Zaux.Zcompare_Gt.
           ++ simpl.
              Exists head_pl head_pr.
              entailer!.
           ++ apply search_path_is_subtree in H0.
              apply wo_subtree_right in H0; try assumption.
              apply is_subtree_up_right in H0.
              inversion H; subst.
              eapply subtree_forall in H0; [|eassumption].
              inversion H0; subst.
              simpl in *; lia.
Admitted.

Lemma no_infinite_node_left {A} : forall (a: A) l r,
  node a l r <> l.
Proof.
  unfold not.
  intros.
  induction l.
  - discriminate.
  - apply IHl1.
    inversion H.
    rewrite H2 at 1.
    reflexivity.
Qed.

Lemma no_infinite_node_right {A} : forall (a: A) l r,
  node a l r <> r.
Proof.
  unfold not.
  intros.
  induction r.
  - discriminate.
  - apply IHr2.
    inversion H.
    rewrite H3 at 1.
    reflexivity.
Qed.

Fixpoint depth {A} (b: bin_tree A) : nat := 
  match b with 
  | leaf => 0
  | node a l r => S (max (depth l) (depth r))
  end.

Theorem subtree_depth_monotonic {A} : forall (b1 b2: bin_tree A),
  is_subtree b1 b2 -> (depth b1 <= depth b2)%nat.
Proof.
  intros.
  dependent induction H; simpl; lia.
Qed.

Theorem no_subtree_cycle_left {A} : forall (a: A) l r,
  not (is_subtree (node a l r) l).
Proof.
  unfold not.
  intros.
  apply subtree_depth_monotonic in H.
  simpl in H.
  lia.
Qed.

Theorem no_subtree_cycle_right {A} : forall (a: A) l r,
  not (is_subtree (node a l r) r).
Proof.
  unfold not.
  intros.
  apply subtree_depth_monotonic in H.
  simpl in H.
  lia.
Qed.

Theorem body_search_bst: semax_body Vprog Gprog f_search_bst search_bst_spec.
Proof.
  start_function.
  forward_loop (
    EX curr_b curr,
      PROP (search_path k b curr_b; curr_b = b -> curr = head)
      LOCAL (
        gvars gv; temp _bst__1 curr;
        temp _key (Vint (Int.repr k)))
      SEP (
        bst_hole_rep (bst_subtract_path k b curr_b) head;
        bst_rep curr_b curr; mem_mgr gv)
  ).
  {
    repeat EExists.
    entailer!.
    - constructor.
    - rewrite bst_subtract_path_b_b.
      entailer!.
  }
  Intros curr_b curr.
  forward_if.
  {
    forward.
    simplify_assumps; subst.
    rewrite search_path_fail by assumption.
    EExists.
    entailer!.
    simpl.
    entailer!.
  }
  assert_PROP (curr_b <> leaf) by (expand bst_rep; entailer!; find_contradiction). 
  destruct curr_b as [|[curr_k v] l r]; [contradiction|].
  expand bst_rep.
  Intros pl pr.
  forward.
  forward_if.
  {
    assert (k = curr_k).
    { apply repr_inj_signed; try assumption.
      apply search_path_is_subtree in H2.
      pose proof (subtree_forall _ _ _ H2 H0) as H11.
      inversion H11; simpl in *; assumption. }
    subst.
    forward.
    EExists.
    simpl.
    entailer!.
    erewrite search_path_success by eassumption.
    sep_apply generalize_node_rep.
    cancel.
  }
  forward.
  forward_if.
  - assert (k < curr_k).
    {
      rewrite <- Int.signed_repr.
      - assumption.
      - apply search_path_is_subtree in H2.
        eapply subtree_forall in H2; [|eassumption].
        inversion H2; subst.
        simpl in H11; assumption.
    }
    forward.
    Exists l pl.
    entailer!.
    + split.
      * eapply path_step_down_l; eassumption.
      * intro; subst.
        apply search_path_is_subtree in H2.
        apply no_subtree_cycle_left in H2.
        contradiction.
    + apply hole_rep_fuse_left; assumption.
  - assert (k > curr_k).
    {
      apply search_path_is_subtree in H2.
      pose proof (subtree_forall _ _ _ H2 H0) as H8.
      rewrite Int.signed_repr in H7.
      + enough (k <> curr_k). lia.
        apply repr_inj_signed'; try assumption.
        inversion H8; simpl in *; assumption.
      + inversion H8; simpl in *; assumption.
    }
    forward.
    Exists r pr.
    entailer!.
    + split.
      * eapply path_step_down_r; [eassumption|lia].
      * intro; subst.
        apply search_path_is_subtree in H2.
        apply no_subtree_cycle_right in H2.
        contradiction.
    + apply hole_rep_fuse_right; assumption.
Qed.

Definition ptr_to_bst_rep b p := EX q, data_at Ews (tptr t_bst) q p * bst_rep b q.

Theorem generalize_ptr_to_node_rep : forall b p q,
  data_at Ews (tptr t_bst) q p * bst_rep b q |-- ptr_to_bst_rep b p.
Proof.
  intros.
  unfold ptr_to_bst_rep.
  EExists.
  entailer!.
Qed.

(* Definition bst_hole_ptr_rep b p :=
  match b with
  | hole => emp
  | _ => EX q, data_at Ews (tptr t_bst) q p * bst_hole_rep b q
  end. *)
Print bst_hole_rep.
Fixpoint ptr_to_bst_hole_rep b p := 
  match b with 
  | hole => emp
  | node_hole_l (k,v) l r =>
      EX (q pr: val),
        data_at Ews (tptr t_bst) q p *
        malloc_token Ews t_bst q *
        field_at Ews t_bst [StructField _key] (Vint (Int.repr k)) q *
        field_at Ews t_bst [StructField _val] (Vint (Int.repr v)) q *
        field_at Ews t_bst [StructField _right] pr q *
        ptr_to_bst_hole_rep l (field_address t_bst [StructField _left] q) *
        bst_rep r pr
  | node_hole_r (k,v) l r =>
      EX (q pl: val),
        data_at Ews (tptr t_bst) q p *
        malloc_token Ews t_bst q *
        field_at Ews t_bst [StructField _key] (Vint (Int.repr k)) q *
        field_at Ews t_bst [StructField _val] (Vint (Int.repr v)) q *
        field_at Ews t_bst [StructField _left] pl q *
        bst_rep l pl *
        ptr_to_bst_hole_rep r (field_address t_bst [StructField _right] q)
  end.

Theorem body_insert_bst: semax_body Vprog Gprog f_insert_bst insert_bst_spec.
Proof.
  start_function.
  forward_loop (
    EX curr_b curr_ptr,
      PROP (
        search_path k b curr_b;
        curr_b = b -> curr_ptr = bst_ptr)
      LOCAL (
        gvars gv; temp _bst__1 curr_ptr;
        temp _key (Vint (Int.repr k));
        temp _val (Vint (Int.repr v)))
      SEP (
        ptr_to_bst_hole_rep (bst_subtract_path k b curr_b) bst_ptr;
        ptr_to_bst_rep curr_b curr_ptr;
        mem_mgr gv)
  ).
  {
    Exists b bst_ptr.
    entailer!.
    - constructor.
    - rewrite bst_subtract_path_b_b.
      simpl. cancel.
      unfold ptr_to_bst_rep.
      Exists head.
      entailer!.
  }
  unfold ptr_to_bst_rep.
  Intros curr_b curr_ptr curr.
  forward.
  forward_if.
  {
    subst.
    forward_call.
    Intros vret.
    repeat forward.
    simplify_assumps; subst.
    simpl bst_rep at 2; entailer!.

    revert H3 H4.
    clear.
    generalize dependent bst_ptr.
    induction b; intros.
    - simpl.
      simplify_assumps; subst.
      Intros pl pr.
      Exists vret pl pr.
      entailer!.
    - clear H4.
      simpl bst_subtract_path.
      destruct_pair.
      find_Z_compare_destruct.
      + apply search_path_fail in H3.
        simpl in H3.
        rewrite Z.compare_refl in H3.
        discriminate H3.
      + simpl bst_subtract_path in *.
        simpl ptr_to_bst_hole_rep.
        Intros q pr.
        (* sep_apply (IHb1 (field_address t_bst [StructField _left] q)). *)
        sep_apply IHb1.
        * inversion H3; subst; [assumption | lia].
        * admit.
        * Intros a.
          Exists q.
          entailer!.
          simpl.
          rewrite Zaux.Zcompare_Lt by assumption.
          simpl.
          Exists a pr.
          entailer!.
          unfold_data_at (data_at _ _ _ q).
          entailer!.
      + simpl bst_subtract_path in *.
        simpl ptr_to_bst_hole_rep.
        Intros q pl.
        (* sep_apply (IHb2 (field_address t_bst [StructField _right] q)). *)
        sep_apply IHb2.
        * inversion H3; subst; [lia | assumption].
        * admit.
        * Intros a.
          Exists q.
          entailer!.
          simpl.
          rewrite Zaux.Zcompare_Gt by lia.
          simpl.
          Exists pl a.
          entailer!.
          unfold_data_at (data_at _ _ _ q).
          entailer!.
  }
  assert_PROP (curr_b <> leaf) by (expand bst_rep; entailer!; find_contradiction). 
  destruct curr_b as [|[curr_k curr_v] l r]; [contradiction|].
  expand bst_rep.
  Intros pl pr.
  repeat forward.
  forward_if.
  {
    repeat forward.
    assert (k = curr_k).
    { apply repr_inj_signed; try assumption.
      apply search_path_is_subtree in H3.
      eapply subtree_forall in H3; [|eassumption].
      inversion H3; simpl in *; assumption. }
    subst.
    simpl.
    sep_apply generalize_node_rep.
    sep_apply generalize_ptr_to_node_rep.

    assert ((
      ptr_to_bst_rep (insert curr_k v b) bst_ptr * mem_mgr gv
      =
      EX a : val,
      data_at Ews (tptr t_bst) a bst_ptr *
      (bst_rep (insert curr_k v b) a * mem_mgr gv)
    )%logic).
    { apply pred_ext; unfold ptr_to_bst_rep; Intros q; Exists q; entailer!. }
    rewrite <- H15.
    entailer!.

    revert H2 H3 H4.   
    clear.
    revert bst_ptr.
    induction b; intros.
    - inversion H3.
    - simpl.
      destruct_pair.
      find_Z_compare_destruct.
      + simpl; cancel.
        apply search_path_is_subtree in H3.
        apply wo_node_eq in H3; [|assumption].
        inversion H3; subst.
        simplify_assumps; subst.
        entailer!.
      + simpl.
        Intros q pr.
        sep_apply IHb1.
        * inversion H2; assumption.
        * inversion H3; subst; lia + assumption.
        * admit.
        * unfold ptr_to_bst_rep.
          Intros pl.
          Exists q.
          entailer!.
          simpl.
          Exists pl pr.
          unfold_data_at (data_at _ _ _ q).
          entailer!.
      + simpl.
        Intros q pl.
        sep_apply IHb2.
        * inversion H2; assumption.
        * inversion H3; subst; lia + assumption.
        * admit.
        * unfold ptr_to_bst_rep.
          Intros pr.
          Exists q.
          entailer!.
          simpl.
          Exists pl pr.
          unfold_data_at (data_at _ _ _ q).
          entailer!.
  }
  repeat forward.
  forward_if.
  {
    assert (k < curr_k).
    {
      rewrite <- Int.signed_repr.
      - assumption.
      - apply search_path_is_subtree in H3.
        eapply subtree_forall in H3; [|eassumption].
        inversion H3; subst.
        simpl in *; assumption.
    }
    repeat forward.
    simpl offset_val.
    entailer!.
    Exists l (field_address t_bst [StructField _left] curr).
    entailer!.
    - split.
      + eapply path_step_down_l; eassumption.
      + intro; subst.
        apply search_path_is_subtree in H3.
        apply no_subtree_cycle_left in H3.
        contradiction.
    - sep_apply generalize_node_rep.
      simpl bst_subtract_path.
      revert bst_ptr H2 H3 H4.   
      clear - H9.
      induction b; intros; [inversion H3|].
      simpl.
      Intros pl pr.
      destruct_pair.
      find_Z_compare_destruct.
      + apply search_path_is_subtree in H3.
        apply wo_node_eq in H3; [|assumption].
        inversion H3; subst.
        simplify_assumps; subst.
        destruct l.
        * simpl.
          rewrite Zaux.Zcompare_Lt by assumption.
          simpl.
          unfold ptr_to_bst_rep.
          Exists curr pr pl.
          expand bst_rep.
          unfold_data_at (data_at _ _ _ curr).
          entailer!.
        * simpl.
          destruct_pair.
          Intros pl' pr'.
          rewrite Z.compare_refl.
          rewrite Zaux.Zcompare_Lt.
          -- simpl.
             unfold ptr_to_bst_rep.
             Exists curr pr pl.
             unfold_data_at (data_at _ _ _ curr).
             entailer!.
             apply generalize_node_rep.
          -- inversion H2; subst.
             inversion H4; subst.
             simpl in H3; assumption.
      + simpl.
        Intros q pr'.
        sep_apply generalize_node_rep.
        sep_apply IHb1.
        * inversion H2; assumption.
        * inversion H3; lia + assumption.
        * admit.
        * entailer!.
          destruct l.
          -- simpl.
             rewrite Zaux.Zcompare_Lt.
             ++ simpl.
                Exists q pr'.
                entailer!.
             ++ inversion H3; lia.
          -- simpl.
             destruct_pair.
             rewrite Zaux.Zcompare_Lt.
             ++ simpl.
                Exists q pr'.
                entailer!.
             ++ inversion H3; subst; try lia.
                apply search_path_is_subtree in H20.
                apply subtree_well_ordered in H20; [|inversion H2; assumption].
                inversion H20; subst.
                inversion H18; subst.
                simpl in H17; lia.
      + simpl.
        Intros q pl'.
        sep_apply generalize_node_rep.
        sep_apply IHb2.
        * inversion H2; assumption.
        * inversion H3; subst.
          -- lia.
          -- apply search_path_is_subtree in H10.
             eapply subtree_forall in H10; [| inversion H2; eassumption].
             inversion H10; subst.
             simpl in H6; lia.
          -- assumption.
        * admit.
        * cancel.
          destruct l.
          -- simpl.
             rewrite Zaux.Zcompare_Gt.
             ++ simpl.
                Exists q pl'.
                entailer!.
             ++ inversion H3; subst; try lia.
                apply search_path_is_subtree in H10.
                eapply subtree_forall in H10; [| inversion H2; eassumption].
                inversion H10; subst.
                simpl in H6; lia.
          -- simpl.
             destruct_pair.
             rewrite Zaux.Zcompare_Gt.
             ++ simpl.
                Exists q pl'.
                entailer!.
             ++ apply search_path_is_subtree in H3.
                apply wo_subtree_right in H3; [|assumption|lia].
                apply is_subtree_up_left in H3.
                eapply subtree_forall in H3; [|inversion H2; eassumption].
                inversion H3; subst.
                simpl in H6; lia.
  }
  {
    assert (k > curr_k).
    {
      apply search_path_is_subtree in H3.
      eapply subtree_forall in H3; [|eassumption].
      rewrite Int.signed_repr in H8.
      + enough (k <> curr_k). lia.
        apply repr_inj_signed'; try assumption.
        inversion H3; simpl in *; assumption.
      + inversion H3; simpl in *; assumption.
    }
    repeat forward.
    simpl offset_val.
    entailer!.
    Exists r (field_address t_bst [StructField _right] curr).
    entailer!.
    - split.
      + eapply path_step_down_r; eassumption + lia.
      + intro; subst.
        apply search_path_is_subtree in H3.
        apply no_subtree_cycle_right in H3.
        contradiction.
    - sep_apply generalize_node_rep.
      simpl bst_subtract_path.
      revert bst_ptr H2 H3 H4.   
      clear - H9.
      induction b; intros; [inversion H3|].
      simpl.
      Intros pl pr.
      destruct_pair.
      find_Z_compare_destruct.
      + apply search_path_is_subtree in H3.
        apply wo_node_eq in H3; [|assumption].
        inversion H3; subst.
        simplify_assumps; subst.
        destruct r.
        * simpl.
          rewrite Zaux.Zcompare_Gt by lia.
          simpl.
          unfold ptr_to_bst_rep.
          Exists curr pl pr.
          expand bst_rep.
          unfold_data_at (data_at _ _ _ curr).
          entailer!.
        * simpl.
          destruct_pair.
          Intros pl' pr'.
          rewrite Z.compare_refl.
          rewrite Zaux.Zcompare_Gt.
          -- simpl.
             unfold ptr_to_bst_rep.
             Exists curr pl pr.
             unfold_data_at (data_at _ _ _ curr).
             entailer!.
             apply generalize_node_rep.
          -- inversion H2; subst.
             inversion H5; subst.
             simpl in H3; lia.
      + simpl.
        Intros q pr'.
        sep_apply generalize_node_rep.
        sep_apply IHb1.
        * inversion H2; assumption.
        * inversion H3; subst.
          -- lia.
          -- assumption.
          -- apply search_path_is_subtree in H10.
             eapply subtree_forall in H10; [| inversion H2; eassumption].
             inversion H10; subst.
             simpl in H6; lia.
        * admit.
        * cancel.
          destruct r.
          -- simpl.
             rewrite Zaux.Zcompare_Lt.
             ++ simpl.
                Exists q pr'.
                entailer!.
             ++ inversion H3; subst.
                ** lia.
                ** assumption.   
                ** apply search_path_is_subtree in H10.
                   eapply subtree_forall in H10; [| inversion H2; eassumption].
                   inversion H10; subst.
                   simpl in H6; lia.
          -- simpl.
             destruct_pair.
             rewrite Zaux.Zcompare_Lt.
             ++ simpl.
                Exists q pr'.
                entailer!.
             ++ inversion H3; subst.
                ** lia.
                ** apply search_path_is_subtree in H10.
                   apply is_subtree_up_right in H10.
                   eapply subtree_forall in H10; [| inversion H2; eassumption].
                   inversion H10; subst.
                   simpl in H6; lia.
                ** apply search_path_is_subtree in H10.
                   eapply subtree_forall in H10; [| inversion H2; eassumption].
                   inversion H10; subst.
                   simpl in H6; lia.
      + simpl.
        Intros q pl'.
        sep_apply generalize_node_rep.
        sep_apply IHb2.
        * inversion H2; assumption.
        * inversion H3; subst.
          -- lia.
          -- apply search_path_is_subtree in H10.
             eapply subtree_forall in H10; [| inversion H2; eassumption].
             inversion H10; subst.
             simpl in H6; lia.
          -- assumption.
        * admit.
        * cancel.
          destruct r.
          -- simpl.
             rewrite Zaux.Zcompare_Gt.
             ++ simpl.
                Exists q pl'.
                entailer!.
             ++ inversion H3; lia.
          -- simpl.
             destruct_pair.
             rewrite Zaux.Zcompare_Gt.
             ++ simpl.
                Exists q pl'.
                entailer!.
             ++ apply search_path_is_subtree in H3.
                apply wo_subtree_right in H3; [|assumption|lia].
                apply is_subtree_up_right in H3.
                eapply subtree_forall in H3; [|inversion H2; eassumption].
                inversion H3; subst.
                simpl in H6; lia.
  }
Admitted.