Require Import VST.floyd.proofauto.
Require Import Coq.Program.Equality.

Require Import my_tactics.

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

Theorem bin_tree_forall_strengthen {A} : forall (p q: A -> Prop) b,
  (forall x, p x -> q x) -> bin_tree_forall b p -> bin_tree_forall b q.
Proof.
  intros.
  dependent induction H0; subst; constructor; simplify_assumps.
  - apply H. assumption.
  - assumption.
  - assumption.
Qed.

Inductive well_ordered {A} : bin_tree (Z * A) -> Prop :=
  | well_ordered_leaf : well_ordered leaf 
  | well_ordered_node : forall k v l r,
      bin_tree_forall l (fun n => fst n < k) -> 
      bin_tree_forall r (fun n => fst n > k) -> 
      well_ordered l ->
      well_ordered r ->
      well_ordered (node (k, v) l r).

Definition bst A := bin_tree (Z * A).

(* Subtrees *)

Inductive is_subtree {A} : bin_tree A -> bin_tree A -> Prop :=
  | is_subtree_refl  : forall b, is_subtree b b 
  | is_subtree_left  : forall b n l r, is_subtree b l -> is_subtree b (node n l r)
  | is_subtree_right : forall b n l r, is_subtree b r -> is_subtree b (node n l r).

(* Definition proper_subtree {A} (b1 b2: bin_tree A) := b1 <> b2 /\ is_subtree b1 b2. *)

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
  try (apply IHis_subtree; inv H0);
  assumption.
Qed.

Theorem subtree_well_ordered : forall {A} (b sub: bst A),
  is_subtree sub b -> well_ordered b -> well_ordered sub.
Proof.
  intros.
  induction b.
  - destruct sub.
    + constructor.
    + inv H.
  - inv H.
    + assumption.
    + inv H0; apply IHb1; assumption.
    + inv H0; apply IHb2; assumption.
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

Lemma no_infinite_node_left {A} : forall (a: A) l r,
  node a l r <> l.
Proof.
  unfold not.
  intros.
  induction l.
  - discriminate.
  - apply IHl1.
    inv H.
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
    inv H.
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

Lemma wo_node_eq {A} : forall k (v1 v2: A) l1 l2 r1 r2,
  well_ordered (node (k,v1) l1 r1) ->
  is_subtree (node (k,v2) l2 r2) (node (k,v1) l1 r1) ->
  node (k,v1) l1 r1 = node (k,v2) l2 r2.
Proof.
  intros.
  inv H0.
  - reflexivity. 
  - inv H. 
    eapply subtree_forall in H3; [|eassumption].
    inv H3.
    simpl in H5. lia.
  - inv H.
    eapply subtree_forall in H3; [|eassumption].
    inv H3.
    simpl in H5. lia.
Qed.

Lemma wo_subtree_left {A} : forall k1 k2 (v1 v2: A) l1 l2 r1 r2,
  well_ordered (node (k1,v1) l1 r1) ->
  is_subtree (node (k2,v2) l2 r2) (node (k1,v1) l1 r1) ->
  k2 < k1 ->
  is_subtree (node (k2,v2) l2 r2) l1.
Proof.
  intros.
  inv H0.
  - lia.
  - assumption.
  - inv H.
    eapply subtree_forall in H4; [|eassumption].
    inv H4.
    simpl in H6. lia.
Qed.

Lemma wo_subtree_right {A} : forall k1 k2 (v1 v2: A) l1 l2 r1 r2,
  well_ordered (node (k1,v1) l1 r1) ->
  is_subtree (node (k2,v2) l2 r2) (node (k1,v1) l1 r1) ->
  k2 > k1 ->
  is_subtree (node (k2,v2) l2 r2) r1.
Proof.
  intros.
  inv H0.
  - lia.
  - inv H.
    eapply subtree_forall in H4; [|eassumption].
    inv H4.
    simpl in H6. lia.
  - assumption.
Qed.

(* Search *)

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

Theorem search_spec {A} : forall (b: bst A) k v l r,
  well_ordered b ->
  is_subtree (node (k,v) l r) b ->
  search k b = node (k,v) l r.
Proof.
  intros.
  induction b.
  - inv H0.
  - inv H.
    simplify_assumps.
    simpl.
    find_Z_compare_destruct.
    + eapply wo_node_eq; assumption.
    + apply IHb1.
      eapply wo_subtree_left; eassumption.
    + apply IHb2.
      eapply wo_subtree_right; eassumption.
Qed.

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

(* Insert *)

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
    inv H0; constructor; 
    try (apply IHb1 + apply IHb2); 
    assumption.
Qed.

Theorem insert_well_ordered {A}: forall (b: bst A) k v, 
  well_ordered b -> well_ordered (insert k v b).
Proof.
  intro b; induction b; intros k v H; simpl.
  - repeat constructor.
  - inv H.
    find_Z_compare_destruct;
    constructor; try (apply insert_forall + apply IHb1 + apply IHb2); assumption.
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

(* Delete *)

Fixpoint get_min {A} (a: Z * A) (l r: bst A) : Z * A :=
  match l with
  | leaf => a
  | node a' l' r' => get_min a' l' r'
  end.

Fixpoint rm_min {A} (a: Z * A) (l r: bst A) : bst A :=
  match l with
  | leaf => r
  | node a' l' r' => node a (rm_min a' l' r') r
  end.

Lemma get_min_forall {A} : forall (p: (Z * A) -> Prop) a l r,
  bin_tree_forall (node a l r) p -> p (get_min a l r).
Proof.
  intros p a l; revert p a.
  induction l; intros; simpl.
  - inv H; assumption.
  - apply IHl1.
    inv H; assumption.
Qed.

Lemma rm_min_forall {A} : forall (p: (Z * A) -> Prop) a l r,
  bin_tree_forall (node a l r) p -> bin_tree_forall (rm_min a l r) p.
Proof.
  intros p a l; revert p a.
  induction l; intros; simpl.
  - inv H; assumption.
  - constructor.
    + inv H; assumption.
    + apply IHl1. inv H; assumption.
    + inv H; assumption.
Qed.

Lemma get_min_is_min {A} : forall (a: Z * A) l r,
  well_ordered (node a l r) ->
  bin_tree_forall (rm_min a l r) (fun n => fst n > fst (get_min a l r)).
Proof.
  intros a l; revert a.
  induction l; intros; simpl.
  - inv H; assumption.
  - constructor.
    + inv H.
      apply get_min_forall in H3.
      simpl. lia.
    + apply IHl1. inv H; assumption.
    + inv H.
      eapply bin_tree_forall_strengthen; [|eassumption].
      intros [x].
      simpl.
      enough (k > fst (get_min a l1 l2)); [lia|].
      apply get_min_forall in H3.
      lia.
Qed.

Lemma get_min_is_min_2 {A} : forall (a: Z * A) l r,
  well_ordered (node a l r) ->
  bin_tree_forall (node a l r) (fun n => fst n >= fst (get_min a l r)).
Proof.
  intros a l; revert a.
  induction l; intros; simpl.
  - inv H.
    constructor.
    + lia.
    + constructor.
    + simpl.
      eapply bin_tree_forall_strengthen; [|eassumption]. 
      intros [x].
      lia.
  - inv H.
    constructor.
    + specialize (IHl1 a l2 H5).
      inv IHl1.
      simpl.
      inv H3.
      lia.
    + apply IHl1.
      assumption.
    + eapply bin_tree_forall_strengthen; [|eassumption]. 
      intros [x].
      simpl.
      enough (k > fst (get_min a l1 l2)); [lia|].
      apply get_min_forall in H3.
      lia.
Qed.

Theorem rm_min_well_ordered {A} : forall (a: Z * A) l r,
  well_ordered (node a l r) -> well_ordered (rm_min a l r).
Proof.
  intros a l; revert a.
  induction l; intros; simpl.
  - inv H; assumption.
  - destruct a0; constructor.
    + apply rm_min_forall. inv H; assumption.
    + inv H; assumption.
    + apply IHl1. inv H; assumption.
    + inv H; assumption.
Qed.

Fixpoint delete {A} (k: Z) (b: bst A) : bst A := 
  match b with 
  | leaf => leaf
  | node (k', v) l r => 
      match k ?= k' with 
      | Eq => match l with
          | leaf => r
          | _ => match r with 
              | leaf => leaf
              | node ra rl rr => node (get_min ra rl rr) l (rm_min ra rl rr)
              end
          end
      | Lt => delete k l
      | Gt => delete k r
      end 
  end.

Lemma delete_forall {A} : forall (p: (Z * A) -> Prop) k bst,
  bin_tree_forall bst p -> bin_tree_forall (delete k bst) p.
Proof.
  intros p k b.
  induction b as [|[k' v] l IH1 r IH2]; intro H; simpl; [assumption|].
  find_Z_compare_destruct.
  - destruct l, r; try (inv H; assumption).
    constructor.
    + apply get_min_forall.
      inv H; assumption.
    + inv H; assumption.
    + apply rm_min_forall.
      inv H; assumption.
  - apply IH1. inv H; assumption.
  - apply IH2. inv H; assumption.
Qed.

Theorem delete_well_ordered {A}: forall (b: bst A) k, 
  well_ordered b -> well_ordered (delete k b).
Proof.
  intros b; induction b as [|[k' v] l IH1 r IH2]; intros k H; simpl; [constructor|].
  find_Z_compare_destruct.
  - destruct l, r; try (inv H; assumption).
    destruct (get_min p0 r1 r2) eqn:H_min.
    constructor.
    + inv H; subst.
      eapply bin_tree_forall_strengthen; [|eassumption].
      intros [x].
      simpl.
      enough (k' < z); [lia|].
      apply get_min_forall in H5.
      rewrite H_min in H5; simpl in H5.
      lia.
    + replace z with (fst (get_min p0 r1 r2)) by (rewrite H_min; reflexivity).
      apply get_min_is_min.
      inv H; assumption.
    + inv H; assumption.
    + apply rm_min_well_ordered.
      inv H; assumption.
  - apply IH1. inv H; assumption.
  - apply IH2. inv H; assumption.
Qed.

(* search_path: This describes a point in a key-search traversal, commonly used to express 
   loop invariants *)

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

Theorem path_shrink_l : forall k_search k k' v v' l l' r r',
  well_ordered (node (k,v) l r) ->
  k' < k ->
  search_path k_search (node (k,v) l r) (node (k',v') l' r') ->
  search_path k_search l (node (k',v') l' r').
Proof.
  intros.
  inv H1.
  - lia.
  - assumption.
  - apply search_path_is_subtree in H8.
    inv H.
    eapply subtree_forall in H8; [|eassumption].
    inv H8.
    simpl in *.
    lia.
Qed.

Theorem path_shrink_r : forall k_search k k' v v' l l' r r',
  well_ordered (node (k,v) l r) ->
  k < k' ->
  search_path k_search (node (k,v) l r) (node (k',v') l' r') ->
  search_path k_search r (node (k',v') l' r').
Proof.
  intros.
  inv H1.
  - lia.
  - apply search_path_is_subtree in H8.
    inv H.
    eapply subtree_forall in H8; [|eassumption].
    inv H8.
    simpl in *.
    lia.
  - assumption.
Qed.

Theorem path_extract_ord_l : forall k_search k k' v v' l l' r r',
  well_ordered (node (k,v) l r) ->
  k' < k ->
  search_path k_search (node (k,v) l r) (node (k',v') l' r') ->
  k_search < k.
Proof.
  intros.
  inv H1.
  - lia.
  - assumption.
  - apply search_path_is_subtree in H8.
    inv H.
    eapply subtree_forall in H8; [|eassumption].
    inv H8.
    simpl in *.
    lia.
Qed.

Theorem path_extract_ord_r : forall k_search k k' v v' l l' r r',
  well_ordered (node (k,v) l r) ->
  k < k' ->
  search_path k_search (node (k,v) l r) (node (k',v') l' r') ->
  k < k_search.
Proof.
  intros.
  inv H1.
  - lia.
  - apply search_path_is_subtree in H8.
    inv H.
    eapply subtree_forall in H8; [|eassumption].
    inv H8.
    simpl in *.
    lia.
  - lia.
Qed.
