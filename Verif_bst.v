Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

(* CompCert-generated representation of bst.c *)
Require Import bst.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Require Import Coq.Program.Equality.

Require Import my_tactics.
Require Import bst_spec.
Require Import bst_holes.

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

Fixpoint bst_hole_rep (b: bst_hole Z) (p pHole: val): mpred :=
  match b with 
  | hole => (!! (p = pHole)) && emp 
  | node_hole_l (k, v) l r =>
      EX pl pr: val,
        malloc_token Ews t_bst p *
        data_at Ews t_bst (Vint (Int.repr k), (Vint (Int.repr v), (pl, pr))) p *
        bst_hole_rep l pl pHole *
        bst_rep r pr
  | node_hole_r (k, v) l r =>
      EX pl pr: val,
        malloc_token Ews t_bst p *
        data_at Ews t_bst (Vint (Int.repr k), (Vint (Int.repr v), (pl, pr))) p *
        bst_rep l pl *
        bst_hole_rep r pr pHole
  end.

Definition ptr_to_bst_rep b p := EX q, data_at Ews (tptr t_bst) q p * bst_rep b q.

Theorem generalize_ptr_to_node_rep : forall b p q,
  data_at Ews (tptr t_bst) q p * bst_rep b q |-- ptr_to_bst_rep b p.
Proof.
  intros.
  unfold ptr_to_bst_rep.
  EExists.
  entailer!.
Qed.

Fixpoint ptr_to_bst_hole_rep b p pHole := 
  match b with 
  | hole => !! (p = pHole) && emp
  | node_hole_l (k,v) l r =>
      EX (q pr: val),
        data_at Ews (tptr t_bst) q p *
        malloc_token Ews t_bst q *
        field_at Ews t_bst [StructField _key] (Vint (Int.repr k)) q *
        field_at Ews t_bst [StructField _val] (Vint (Int.repr v)) q *
        field_at Ews t_bst [StructField _right] pr q *
        ptr_to_bst_hole_rep l (field_address t_bst [StructField _left] q) pHole *
        bst_rep r pr
  | node_hole_r (k,v) l r =>
      EX (q pl: val),
        data_at Ews (tptr t_bst) q p *
        malloc_token Ews t_bst q *
        field_at Ews t_bst [StructField _key] (Vint (Int.repr k)) q *
        field_at Ews t_bst [StructField _val] (Vint (Int.repr v)) q *
        field_at Ews t_bst [StructField _left] pl q *
        bst_rep l pl *
        ptr_to_bst_hole_rep r (field_address t_bst [StructField _right] q) pHole
  end.

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

Definition new_bst_spec: ident * funspec :=
  DECLARE _new_bst
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
      PROP ()
      RETURN (vret)
      SEP (bst_hole_rep (search_make_hole k b) head vret; bst_rep (search k b) vret; mem_mgr gv).

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

Definition pop_min_spec: ident * funspec :=
  DECLARE _pop_min
  WITH bst_ptr: val, head: val, a: (Z * Z), l: bst Z, r: bst Z, gv: globals
  PRE [tptr (tptr t_bst)]
    PROP (bin_tree_forall (node a l r) (fun n => repable_signed (fst n));
          well_ordered (node a l r))
    PARAMS (bst_ptr) GLOBALS (gv)
    SEP (data_at Ews (tptr t_bst) head bst_ptr;
         bst_rep (node a l r) head;
         mem_mgr gv)
  POST [tptr t_bst]
    EX min: val, EX new_bst: val, EX r': bst Z,
      PROP ()
      RETURN (min)
      SEP (data_at Ews (tptr t_bst) new_bst bst_ptr; 
           bst_rep (rm_min a l r) new_bst;
           (* Does this need to be a hole instead? *)
           bst_rep (node (get_min a l r) leaf r') min;
           mem_mgr gv).

Definition delete_bst_spec: ident * funspec :=
  DECLARE _delete_bst
  WITH parent_ptr: val, parent: val, k: Z, b: bst Z, gv: globals
  PRE [tptr (tptr t_bst), tint]
    PROP (repable_signed k;
          bin_tree_forall b (fun n => repable_signed (fst n));
          well_ordered b)
    PARAMS (parent_ptr; Vint (Int.repr k)) GLOBALS (gv)
    SEP (data_at Ews (tptr t_bst) parent parent_ptr;
         bst_rep b parent;
         mem_mgr gv)
  POST [tvoid]
    EX new_bst: val,
      PROP ()
      RETURN ()
      SEP (data_at Ews (tptr t_bst) new_bst parent_ptr; 
           bst_rep (delete k b) new_bst;
           mem_mgr gv).

Definition Gprog: funspecs := 
  ltac:(with_library prog [new_bst_spec; search_bst_spec; insert_bst_spec; pop_min_spec; delete_bst_spec]).

(* Proofs of C functions *)

Theorem hole_rep_fuse_left : forall b k curr_k v l r (curr head pl pr: val),
  well_ordered b ->
  search_path k b (node (curr_k, v) l r) ->
  k < curr_k -> 
    bst_hole_rep (bst_subtract_path k b (node (curr_k, v) l r)) head curr *
    malloc_token Ews t_bst curr *
    data_at Ews t_bst (Vint (Int.repr curr_k), (Vint (Int.repr v), (pl, pr))) curr *
    bst_rep r pr
    |-- bst_hole_rep (bst_subtract_path k b l) head pl.
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
        -- apply search_path_is_subtree in H9.
           inversion H; subst.
           eapply subtree_forall in H9; [|eassumption].
           inversion H9; subst.
           simpl in *.
           lia.
      * destruct l.
        -- simpl. 
           rewrite Zaux.Zcompare_Lt.
           ++ simpl.
              Exists head_pl head_pr.
              entailer!.
           ++ inversion H0; subst.
              ** lia.
              ** assumption.
              ** apply search_path_is_subtree in H9.
                 inversion H; subst.
                 eapply subtree_forall in H9; [|eassumption].
                 inversion H9; subst.
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
        -- apply search_path_is_subtree in H9.
           inversion H; subst.
           eapply subtree_forall in H9; [|eassumption].
           inversion H9; subst.
           simpl in *.
           lia.
        -- assumption.
      * destruct l.
        -- simpl. 
           rewrite Zaux.Zcompare_Gt.
           ++ simpl.
              Exists head_pl head_pr.
              entailer!.
           ++ inversion H0; subst.
              ** lia.
              ** apply search_path_is_subtree in H9.
                 inversion H; subst.
                 eapply subtree_forall in H9; [|eassumption].
                 inversion H9; subst.
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
Qed.

Theorem hole_rep_fuse_right : forall b k curr_k v l r (curr head pl pr: val),
  well_ordered b ->
  search_path k b (node (curr_k, v) l r) ->
  k > curr_k ->
    bst_hole_rep (bst_subtract_path k b (node (curr_k, v) l r)) head curr *
    malloc_token Ews t_bst curr *
    data_at Ews t_bst (Vint (Int.repr curr_k), (Vint (Int.repr v), (pl, pr))) curr *
    bst_rep l pl
    |-- bst_hole_rep (bst_subtract_path k b r) head pr.
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
        -- apply search_path_is_subtree in H9.
           inversion H; subst.
           eapply subtree_forall in H9; [|eassumption].
           inversion H9; subst.
           simpl in *.
           lia.
      * destruct r.
        -- simpl. 
           rewrite Zaux.Zcompare_Lt.
           ++ simpl.
              Exists head_pl head_pr.
              entailer!.
           ++ inversion H0; subst.
              ** lia.
              ** assumption.
              ** apply search_path_is_subtree in H9.
                 inversion H; subst.
                 eapply subtree_forall in H9; [|eassumption].
                 inversion H9; subst.
                 simpl in *.
                 lia.
        -- simpl.
           destruct_pair.
           rewrite Zaux.Zcompare_Lt.
           ++ simpl.
              Exists head_pl head_pr.
              entailer!.
           ++ 
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
        -- apply search_path_is_subtree in H9.
           inversion H; subst.
           eapply subtree_forall in H9; [|eassumption].
           inversion H9; subst.
           simpl in *.
           lia.
        -- assumption.
      * destruct r.
        -- simpl. 
           rewrite Zaux.Zcompare_Gt.
           ++ simpl.
              Exists head_pl head_pr.
              entailer!.
           ++ inversion H0; subst.
              ** lia.
              ** apply search_path_is_subtree in H9.
                 inversion H; subst.
                 eapply subtree_forall in H9; [|eassumption].
                 inversion H9; subst.
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
Qed.

Theorem body_search_bst: semax_body Vprog Gprog f_search_bst search_bst_spec.
Proof.
  start_function.
  forward_loop (
    EX curr_b curr,
      PROP (search_path k b curr_b)
      LOCAL (
        gvars gv; temp _bst__1 curr;
        temp _key (Vint (Int.repr k)))
      SEP (
        bst_hole_rep (bst_subtract_path k b curr_b) head curr;
        bst_rep curr_b curr; mem_mgr gv)
  ).
  {
    repeat EExists.
    entailer!.
    - constructor.
    - rewrite bst_subtract_path_b_b.
      unfold bst_hole_rep.
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
        simpl in H10; assumption.
    }
    forward.
    Exists l pl.
    entailer!.
    + eapply path_step_down_l; eassumption.
    + apply hole_rep_fuse_left; assumption.
  - assert (k > curr_k).
    {
      apply search_path_is_subtree in H2.
      pose proof (subtree_forall _ _ _ H2 H0) as H8.
      rewrite Int.signed_repr in H6.
      + enough (k <> curr_k). lia.
        apply repr_inj_signed'; try assumption.
        inversion H8; simpl in *; assumption.
      + inversion H8; simpl in *; assumption.
    }
    forward.
    Exists r pr.
    entailer!.
    + eapply path_step_down_r; [eassumption|lia].
    + apply hole_rep_fuse_right; assumption.
Qed.

Theorem body_insert_bst: semax_body Vprog Gprog f_insert_bst insert_bst_spec.
Proof.
  start_function.
  forward_loop (
    EX curr_b curr_ptr,
      PROP (search_path k b curr_b)
      LOCAL (
        gvars gv; temp _bst__1 curr_ptr;
        temp _key (Vint (Int.repr k));
        temp _val (Vint (Int.repr v)))
      SEP (
        ptr_to_bst_hole_rep (bst_subtract_path k b curr_b) bst_ptr curr_ptr;
        ptr_to_bst_rep curr_b curr_ptr;
        mem_mgr gv)
  ).
  {
    Exists b bst_ptr.
    entailer!.
    - constructor.
    - rewrite bst_subtract_path_b_b.
      simpl.
      entailer!.
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

    revert H3.
    clear.
    generalize dependent bst_ptr.
    induction b; intros.
    - simpl.
      simplify_assumps; subst.
      Intros pl pr.
      Exists vret pl pr.
      entailer!.
    - simpl bst_subtract_path.
      destruct_pair.
      find_Z_compare_destruct.
      + apply search_path_fail in H3.
        simpl in H3.
        rewrite Z.compare_refl in H3.
        discriminate H3.
      + simpl bst_subtract_path in *.
        simpl ptr_to_bst_hole_rep.
        Intros q pr.
        sep_apply IHb1.
        * inversion H3; subst; [assumption | lia].
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
        sep_apply IHb2.
        * inversion H3; subst; [lia | assumption].
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
    )%logic) by (apply pred_ext; unfold ptr_to_bst_rep; Intros q; Exists q; entailer!).
    rewrite <- H14.
    entailer!.

    revert H2 H3.   
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
    - eapply path_step_down_l; eassumption.
    - sep_apply generalize_node_rep.
      simpl bst_subtract_path.
      revert bst_ptr H2 H3.   
      clear - H8.
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
             inversion H5; subst.
             simpl in H3; assumption.
      + simpl.
        Intros q pr'.
        sep_apply generalize_node_rep.
        sep_apply IHb1.
        * inversion H2; assumption.
        * inversion H3; lia + assumption.
        * cancel.
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
                apply search_path_is_subtree in H9.
                apply subtree_well_ordered in H9; [|inversion H2; assumption].
                inversion H9; subst.
                inversion H6; subst.
                simpl in H5; lia.
      + simpl.
        Intros q pl'.
        sep_apply generalize_node_rep.
        sep_apply IHb2.
        * inversion H2; assumption.
        * inversion H3; subst.
          -- lia.
          -- apply search_path_is_subtree in H9.
             eapply subtree_forall in H9; [| inversion H2; eassumption].
             inversion H9; subst.
             simpl in H5; lia.
          -- assumption.
        * cancel.
          destruct l.
          -- simpl.
             rewrite Zaux.Zcompare_Gt.
             ++ simpl.
                Exists q pl'.
                entailer!.
             ++ inversion H3; subst; try lia.
                apply search_path_is_subtree in H9.
                eapply subtree_forall in H9; [| inversion H2; eassumption].
                inversion H9; subst.
                simpl in H5; lia.
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
                simpl in H5; lia.
  }
  {
    assert (k > curr_k).
    {
      apply search_path_is_subtree in H3.
      eapply subtree_forall in H3; [|eassumption].
      rewrite Int.signed_repr in H7.
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
    - eapply path_step_down_r; eassumption + lia.
    - sep_apply generalize_node_rep.
      simpl bst_subtract_path.
      revert bst_ptr H2 H3.   
      clear - H8.
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
             inversion H6; subst.
             simpl in H3; lia.
      + simpl.
        Intros q pr'.
        sep_apply generalize_node_rep.
        sep_apply IHb1.
        * inversion H2; assumption.
        * inversion H3; subst.
          -- lia.
          -- assumption.
          -- apply search_path_is_subtree in H9.
             eapply subtree_forall in H9; [| inversion H2; eassumption].
             inversion H9; subst.
             simpl in H5; lia.
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
                ** apply search_path_is_subtree in H9.
                   eapply subtree_forall in H9; [| inversion H2; eassumption].
                   inversion H9; subst.
                   simpl in H5; lia.
          -- simpl.
             destruct_pair.
             rewrite Zaux.Zcompare_Lt.
             ++ simpl.
                Exists q pr'.
                entailer!.
             ++ inversion H3; subst.
                ** lia.
                ** apply search_path_is_subtree in H9.
                   apply is_subtree_up_right in H9.
                   eapply subtree_forall in H9; [| inversion H2; eassumption].
                   inversion H9; subst.
                   simpl in H5; lia.
                ** apply search_path_is_subtree in H9.
                   eapply subtree_forall in H9; [| inversion H2; eassumption].
                   inversion H9; subst.
                   simpl in H5; lia.
      + simpl.
        Intros q pl'.
        sep_apply generalize_node_rep.
        sep_apply IHb2.
        * inversion H2; assumption.
        * inversion H3; subst.
          -- lia.
          -- apply search_path_is_subtree in H9.
             eapply subtree_forall in H9; [| inversion H2; eassumption].
             inversion H9; subst.
             simpl in H5; lia.
          -- assumption.
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
                simpl in H5; lia.
  }
Qed.

(* Proofs incomplete / outdated beyond this point *)

Theorem path_shrink_l : forall k k' v l r b,
  (* well_ordered (node (k',v) l r) -> *)
  node (k',v) l r <> b ->
  k < k' -> search_path k (node (k',v) l r) b -> search_path k l b.
Proof.
  (* intros.
  induction l.
  - inversion H2; subst.
    + contradiction.
    + assumption.
    + lia.
  - destruct a.
    reflect_destruct_Z_compare k z.
    + inversion H1; subst; try lia.
      *  *)
Admitted.


Theorem body_pop_min: semax_body Vprog Gprog f_pop_min pop_min_spec.
Proof.
  start_function.
  forward_loop (
    EX a' l' r' curr_ptr min_z,
      PROP (
        min_z = fst (get_min a l r);
        search_path min_z (node a l r) (node a' l' r'))
      LOCAL (
        gvars gv; temp _bst_ptr curr_ptr)
      SEP (
        ptr_to_bst_hole_rep (bst_subtract_path min_z (node a l r) (node a' l' r')) bst_ptr curr_ptr;
        ptr_to_bst_rep (node a' l' r') curr_ptr;
        mem_mgr gv)
  ).
  {
    entailer!.
    Exists a l r bst_ptr (fst (get_min a l r)).
    entailer!.
    - constructor.
    - simpl.
      destruct_pair.
      Intros pl pr.
      rewrite Z.compare_refl.
      unfold ptr_to_bst_rep, ptr_to_bst_hole_rep.
      expand bst_rep.
      Exists head pl pr.
      entailer!.
  }
  unfold ptr_to_bst_rep.
  Intros a' l' r' curr_ptr min_z curr.
  expand bst_rep.
  destruct_pair.
  Intros pl pr.
  repeat forward.
  forward_if.
  {
    repeat forward.
    simpl offset_val.
    assert_PROP (l' <> leaf) by (entailer!; find_contradiction).
    destruct l' as [|l'a l'l l'r]; [contradiction|].
    entailer!.
    simplify_assumps; subst.
    Exists l'a l'l l'r (field_address t_bst [StructField _left] curr) (fst (get_min a l r)).
    entailer!.
    - eapply path_step_down_l; [eassumption|].
      apply get_min_is_min in H0.
      admit.
    - 
      sep_apply generalize_node_rep.
      simpl bst_subtract_path.
      repeat destruct_pair.
      rewrite Zaux.Zcompare_Lt.
      rewrite Zaux.Zcompare_Lt.
      + clear - H0 H2.   
        simpl.
        Intros pl pr pl0 pr0 q pr1.
        Exists pl0 pr0.
        cancel.
        unfold ptr_to_bst_rep.
        Exists pl.
        expand bst_rep.
        Exists q pr1.
        cancel.
        unfold_data_at (data_at _ _ _ curr).
        cancel.

        revert z3 z4 r H0 H2 pl0.
        induction l; intros.
        * simpl in H2. inversion H2; lia.
        *
          simpl in *.
          destruct_pair. 
          rewrite Zaux.Zcompare_Lt.
          rewrite Zaux.Zcompare_Lt.
          {
            simpl.
            Intros q0 pr2. Exists q0 pr2.
            sep_apply (IHl1 z5 z6 l2).
            - inversion H0; assumption.
            - eapply path_shrink_l; [| |eassumption].
              + injection; intros; subst. 
                admit.
          }
          admit.
          admit. 
  }
  repeat forward.
  simplify_assumps; subst.
  simpl bst_subtract_path.
  destruct_pair.
  rewrite Zaux.Zcompare_Lt. (* Since search_path puts z towards the min *)
  simpl ptr_to_bst_hole_rep.
  Intros q pr0. (* generalize pr0? *)
  Exists curr q.
  (* EExists. *)
  expand bst_rep.
  destruct (get_min (z1, z2) l r) eqn:H_min.
  (* Exists nullval. *)
  (* EExists. *)
  (* entailer!. *)
  clear - H0 H2 H_min.
  revert pr0.
  induction l; intros.
  - simpl in *.
    inversion H_min; subst.
    inversion H2; subst; try lia.
    simplify_assumps; subst.
Admitted.

Theorem body_delete_bst: semax_body Vprog Gprog f_delete_bst delete_bst_spec.
Proof.
  start_function.
  forward.
  forward_if.
  {
    forward.
    EExists.
    simplify_assumps; subst.
    entailer!.
  }
  assert_PROP (b <> leaf) by (expand bst_rep; entailer!; find_contradiction). 
  destruct b as [|[parent_k v] l r]; [contradiction|].
  expand bst_rep.
  Intros pl pr.
  repeat (forward + forward_if).
  {
    assert_PROP (r <> leaf) by (expand bst_rep; entailer!; find_contradiction). 
    destruct r as [|ra rl rr]; [contradiction|].
    assert_PROP (field_compatible t_bst [StructField _right] parent) by entailer!.
    forward_call(
      field_address t_bst [StructField _right] parent,
      pr, ra, rl, rr, gv).
    - unfold_data_at (data_at _ _ _ parent).
      entailer!.
    - split.
      + inversion H0; assumption.
      + inversion H1; assumption.
    - Intros vret.
      expand bst_rep.
      destruct (get_min ra rl rr) eqn:H_min.
      Intros pl0 pr0.
      repeat forward.
      forward_call(t_bst, fst (fst vret), gv).
      { entailer!.
        apply field_compatible_nullval1 in H15.
        destruct (eq_dec (fst (fst vret)) nullval); [contradiction|].
        entailer!. }
      Exists parent.
      entailer!.
      enough (k = parent_k).
      subst.
      simpl.
      rewrite Z.compare_refl.
      assert_PROP (l <> leaf) by (expand bst_rep; entailer!; find_contradiction). 
      destruct l as [|la ll lr]; [contradiction|].
      expand bst_rep.
      destruct la.
      rewrite H_min.
      Exists pl (snd (fst vret)).
      Intros pl0 pr1; Exists pl0 pr1.
      unfold_data_at (data_at _ _ _ parent).
      entailer!.
      admit.
      admit.
  }
Admitted.
