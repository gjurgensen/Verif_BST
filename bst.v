From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.7"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "64"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "bst.c"%string.
  Definition normalized := true.
End Info.

Definition ___builtin_ais_annot : ident := 6%positive.
Definition ___builtin_annot : ident := 15%positive.
Definition ___builtin_annot_intval : ident := 16%positive.
Definition ___builtin_bswap : ident := 8%positive.
Definition ___builtin_bswap16 : ident := 10%positive.
Definition ___builtin_bswap32 : ident := 9%positive.
Definition ___builtin_bswap64 : ident := 7%positive.
Definition ___builtin_clz : ident := 41%positive.
Definition ___builtin_clzl : ident := 42%positive.
Definition ___builtin_clzll : ident := 43%positive.
Definition ___builtin_ctz : ident := 44%positive.
Definition ___builtin_ctzl : ident := 45%positive.
Definition ___builtin_ctzll : ident := 46%positive.
Definition ___builtin_debug : ident := 57%positive.
Definition ___builtin_fabs : ident := 11%positive.
Definition ___builtin_fmadd : ident := 49%positive.
Definition ___builtin_fmax : ident := 47%positive.
Definition ___builtin_fmin : ident := 48%positive.
Definition ___builtin_fmsub : ident := 50%positive.
Definition ___builtin_fnmadd : ident := 51%positive.
Definition ___builtin_fnmsub : ident := 52%positive.
Definition ___builtin_fsqrt : ident := 12%positive.
Definition ___builtin_membar : ident := 17%positive.
Definition ___builtin_memcpy_aligned : ident := 13%positive.
Definition ___builtin_read16_reversed : ident := 53%positive.
Definition ___builtin_read32_reversed : ident := 54%positive.
Definition ___builtin_sel : ident := 14%positive.
Definition ___builtin_va_arg : ident := 19%positive.
Definition ___builtin_va_copy : ident := 20%positive.
Definition ___builtin_va_end : ident := 21%positive.
Definition ___builtin_va_start : ident := 18%positive.
Definition ___builtin_write16_reversed : ident := 55%positive.
Definition ___builtin_write32_reversed : ident := 56%positive.
Definition ___compcert_i64_dtos : ident := 26%positive.
Definition ___compcert_i64_dtou : ident := 27%positive.
Definition ___compcert_i64_sar : ident := 38%positive.
Definition ___compcert_i64_sdiv : ident := 32%positive.
Definition ___compcert_i64_shl : ident := 36%positive.
Definition ___compcert_i64_shr : ident := 37%positive.
Definition ___compcert_i64_smod : ident := 34%positive.
Definition ___compcert_i64_smulh : ident := 39%positive.
Definition ___compcert_i64_stod : ident := 28%positive.
Definition ___compcert_i64_stof : ident := 30%positive.
Definition ___compcert_i64_udiv : ident := 33%positive.
Definition ___compcert_i64_umod : ident := 35%positive.
Definition ___compcert_i64_umulh : ident := 40%positive.
Definition ___compcert_i64_utod : ident := 29%positive.
Definition ___compcert_i64_utof : ident := 31%positive.
Definition ___compcert_va_composite : ident := 25%positive.
Definition ___compcert_va_float64 : ident := 24%positive.
Definition ___compcert_va_int32 : ident := 22%positive.
Definition ___compcert_va_int64 : ident := 23%positive.
Definition _bst : ident := 3%positive.
Definition _bst__1 : ident := 60%positive.
Definition _del : ident := 69%positive.
Definition _del__1 : ident := 70%positive.
Definition _del__2 : ident := 72%positive.
Definition _del__3 : ident := 73%positive.
Definition _delete_bst : ident := 74%positive.
Definition _free : ident := 59%positive.
Definition _insert_bst : ident := 63%positive.
Definition _key : ident := 1%positive.
Definition _left : ident := 4%positive.
Definition _main : ident := 75%positive.
Definition _malloc : ident := 58%positive.
Definition _min : ident := 67%positive.
Definition _min__1 : ident := 68%positive.
Definition _min__2 : ident := 71%positive.
Definition _new_bst : ident := 61%positive.
Definition _parent : ident := 66%positive.
Definition _parent_ptr : ident := 65%positive.
Definition _pop_min : ident := 64%positive.
Definition _right : ident := 5%positive.
Definition _search_bst : ident := 62%positive.
Definition _val : ident := 2%positive.
Definition _t'1 : ident := 76%positive.
Definition _t'10 : ident := 85%positive.
Definition _t'11 : ident := 86%positive.
Definition _t'12 : ident := 87%positive.
Definition _t'13 : ident := 88%positive.
Definition _t'14 : ident := 89%positive.
Definition _t'15 : ident := 90%positive.
Definition _t'16 : ident := 91%positive.
Definition _t'17 : ident := 92%positive.
Definition _t'18 : ident := 93%positive.
Definition _t'19 : ident := 94%positive.
Definition _t'2 : ident := 77%positive.
Definition _t'20 : ident := 95%positive.
Definition _t'21 : ident := 96%positive.
Definition _t'22 : ident := 97%positive.
Definition _t'23 : ident := 98%positive.
Definition _t'24 : ident := 99%positive.
Definition _t'25 : ident := 100%positive.
Definition _t'26 : ident := 101%positive.
Definition _t'27 : ident := 102%positive.
Definition _t'28 : ident := 103%positive.
Definition _t'29 : ident := 104%positive.
Definition _t'3 : ident := 78%positive.
Definition _t'30 : ident := 105%positive.
Definition _t'31 : ident := 106%positive.
Definition _t'32 : ident := 107%positive.
Definition _t'33 : ident := 108%positive.
Definition _t'34 : ident := 109%positive.
Definition _t'35 : ident := 110%positive.
Definition _t'36 : ident := 111%positive.
Definition _t'37 : ident := 112%positive.
Definition _t'38 : ident := 113%positive.
Definition _t'39 : ident := 114%positive.
Definition _t'4 : ident := 79%positive.
Definition _t'40 : ident := 115%positive.
Definition _t'41 : ident := 116%positive.
Definition _t'42 : ident := 117%positive.
Definition _t'43 : ident := 118%positive.
Definition _t'44 : ident := 119%positive.
Definition _t'45 : ident := 120%positive.
Definition _t'46 : ident := 121%positive.
Definition _t'47 : ident := 122%positive.
Definition _t'48 : ident := 123%positive.
Definition _t'49 : ident := 124%positive.
Definition _t'5 : ident := 80%positive.
Definition _t'50 : ident := 125%positive.
Definition _t'6 : ident := 81%positive.
Definition _t'7 : ident := 82%positive.
Definition _t'8 : ident := 83%positive.
Definition _t'9 : ident := 84%positive.

Definition f_new_bst := {|
  fn_return := (tptr (Tstruct _bst noattr));
  fn_callconv := cc_default;
  fn_params := ((_key, tint) :: (_val, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_bst__1, (tptr (Tstruct _bst noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _bst noattr) tulong) :: nil))
    (Sset _bst__1
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _bst noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _bst__1 (tptr (Tstruct _bst noattr)))
          (Tstruct _bst noattr)) _key tint) (Etempvar _key tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _bst__1 (tptr (Tstruct _bst noattr)))
            (Tstruct _bst noattr)) _val tint) (Etempvar _val tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _bst__1 (tptr (Tstruct _bst noattr)))
              (Tstruct _bst noattr)) _left (tptr (Tstruct _bst noattr)))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _bst__1 (tptr (Tstruct _bst noattr)))
                (Tstruct _bst noattr)) _right (tptr (Tstruct _bst noattr)))
            (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
          (Sreturn (Some (Etempvar _bst__1 (tptr (Tstruct _bst noattr))))))))))
|}.

Definition f_search_bst := {|
  fn_return := (tptr (Tstruct _bst noattr));
  fn_callconv := cc_default;
  fn_params := ((_bst__1, (tptr (Tstruct _bst noattr))) :: (_key, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    Sskip
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _bst__1 (tptr (Tstruct _bst noattr))) tint)
      (Sreturn (Some (Etempvar _bst__1 (tptr (Tstruct _bst noattr)))))
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _bst__1 (tptr (Tstruct _bst noattr)))
              (Tstruct _bst noattr)) _key tint))
        (Sifthenelse (Ebinop Oeq (Etempvar _key tint) (Etempvar _t'1 tint)
                       tint)
          (Sreturn (Some (Etempvar _bst__1 (tptr (Tstruct _bst noattr)))))
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _bst__1 (tptr (Tstruct _bst noattr)))
                  (Tstruct _bst noattr)) _key tint))
            (Sifthenelse (Ebinop Olt (Etempvar _key tint)
                           (Etempvar _t'2 tint) tint)
              (Sset _bst__1
                (Efield
                  (Ederef (Etempvar _bst__1 (tptr (Tstruct _bst noattr)))
                    (Tstruct _bst noattr)) _left
                  (tptr (Tstruct _bst noattr))))
              (Sset _bst__1
                (Efield
                  (Ederef (Etempvar _bst__1 (tptr (Tstruct _bst noattr)))
                    (Tstruct _bst noattr)) _right
                  (tptr (Tstruct _bst noattr))))))))))
  Sskip)
|}.

Definition f_insert_bst := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bst__1, (tptr (tptr (Tstruct _bst noattr)))) ::
                (_key, tint) :: (_val, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _bst noattr))) ::
               (_t'9, (tptr (Tstruct _bst noattr))) ::
               (_t'8, (tptr (Tstruct _bst noattr))) ::
               (_t'7, (tptr (Tstruct _bst noattr))) :: (_t'6, tint) ::
               (_t'5, (tptr (Tstruct _bst noattr))) :: (_t'4, tint) ::
               (_t'3, (tptr (Tstruct _bst noattr))) ::
               (_t'2, (tptr (Tstruct _bst noattr))) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    Sskip
    (Ssequence
      (Sset _t'2
        (Ederef (Etempvar _bst__1 (tptr (tptr (Tstruct _bst noattr))))
          (tptr (Tstruct _bst noattr))))
      (Sifthenelse (Eunop Onotbool
                     (Etempvar _t'2 (tptr (Tstruct _bst noattr))) tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _new_bst (Tfunction (Tcons tint (Tcons tint Tnil))
                               (tptr (Tstruct _bst noattr)) cc_default))
              ((Etempvar _key tint) :: (Etempvar _val tint) :: nil))
            (Sassign
              (Ederef (Etempvar _bst__1 (tptr (tptr (Tstruct _bst noattr))))
                (tptr (Tstruct _bst noattr)))
              (Etempvar _t'1 (tptr (Tstruct _bst noattr)))))
          (Sreturn None))
        (Ssequence
          (Sset _t'3
            (Ederef (Etempvar _bst__1 (tptr (tptr (Tstruct _bst noattr))))
              (tptr (Tstruct _bst noattr))))
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _t'3 (tptr (Tstruct _bst noattr)))
                  (Tstruct _bst noattr)) _key tint))
            (Sifthenelse (Ebinop Oeq (Etempvar _key tint)
                           (Etempvar _t'4 tint) tint)
              (Ssequence
                (Ssequence
                  (Sset _t'9
                    (Ederef
                      (Etempvar _bst__1 (tptr (tptr (Tstruct _bst noattr))))
                      (tptr (Tstruct _bst noattr))))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _t'9 (tptr (Tstruct _bst noattr)))
                        (Tstruct _bst noattr)) _val tint)
                    (Etempvar _val tint)))
                (Sreturn None))
              (Ssequence
                (Sset _t'5
                  (Ederef
                    (Etempvar _bst__1 (tptr (tptr (Tstruct _bst noattr))))
                    (tptr (Tstruct _bst noattr))))
                (Ssequence
                  (Sset _t'6
                    (Efield
                      (Ederef (Etempvar _t'5 (tptr (Tstruct _bst noattr)))
                        (Tstruct _bst noattr)) _key tint))
                  (Sifthenelse (Ebinop Olt (Etempvar _key tint)
                                 (Etempvar _t'6 tint) tint)
                    (Ssequence
                      (Sset _t'8
                        (Ederef
                          (Etempvar _bst__1 (tptr (tptr (Tstruct _bst noattr))))
                          (tptr (Tstruct _bst noattr))))
                      (Sset _bst__1
                        (Eaddrof
                          (Efield
                            (Ederef
                              (Etempvar _t'8 (tptr (Tstruct _bst noattr)))
                              (Tstruct _bst noattr)) _left
                            (tptr (Tstruct _bst noattr)))
                          (tptr (tptr (Tstruct _bst noattr))))))
                    (Ssequence
                      (Sset _t'7
                        (Ederef
                          (Etempvar _bst__1 (tptr (tptr (Tstruct _bst noattr))))
                          (tptr (Tstruct _bst noattr))))
                      (Sset _bst__1
                        (Eaddrof
                          (Efield
                            (Ederef
                              (Etempvar _t'7 (tptr (Tstruct _bst noattr)))
                              (Tstruct _bst noattr)) _right
                            (tptr (Tstruct _bst noattr)))
                          (tptr (tptr (Tstruct _bst noattr)))))))))))))))
  Sskip)
|}.

Definition f_delete_bst := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_parent_ptr, (tptr (tptr (Tstruct _bst noattr)))) ::
                (_key, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_parent, (tptr (Tstruct _bst noattr))) ::
               (_min, (tptr (Tstruct _bst noattr))) ::
               (_min__1, (tptr (Tstruct _bst noattr))) ::
               (_del, (tptr (Tstruct _bst noattr))) ::
               (_del__1, (tptr (Tstruct _bst noattr))) ::
               (_min__2, (tptr (Tstruct _bst noattr))) ::
               (_del__2, (tptr (Tstruct _bst noattr))) ::
               (_del__3, (tptr (Tstruct _bst noattr))) ::
               (_t'3, (tptr (Tstruct _bst noattr))) ::
               (_t'2, (tptr (Tstruct _bst noattr))) ::
               (_t'1, (tptr (Tstruct _bst noattr))) :: (_t'50, tint) ::
               (_t'49, tint) :: (_t'48, (tptr (Tstruct _bst noattr))) ::
               (_t'47, (tptr (Tstruct _bst noattr))) ::
               (_t'46, (tptr (Tstruct _bst noattr))) ::
               (_t'45, (tptr (Tstruct _bst noattr))) ::
               (_t'44, (tptr (Tstruct _bst noattr))) ::
               (_t'43, (tptr (Tstruct _bst noattr))) :: (_t'42, tint) ::
               (_t'41, (tptr (Tstruct _bst noattr))) :: (_t'40, tint) ::
               (_t'39, (tptr (Tstruct _bst noattr))) ::
               (_t'38, (tptr (Tstruct _bst noattr))) ::
               (_t'37, (tptr (Tstruct _bst noattr))) ::
               (_t'36, (tptr (Tstruct _bst noattr))) ::
               (_t'35, (tptr (Tstruct _bst noattr))) ::
               (_t'34, (tptr (Tstruct _bst noattr))) ::
               (_t'33, (tptr (Tstruct _bst noattr))) ::
               (_t'32, (tptr (Tstruct _bst noattr))) ::
               (_t'31, (tptr (Tstruct _bst noattr))) ::
               (_t'30, (tptr (Tstruct _bst noattr))) ::
               (_t'29, (tptr (Tstruct _bst noattr))) ::
               (_t'28, (tptr (Tstruct _bst noattr))) :: (_t'27, tint) ::
               (_t'26, (tptr (Tstruct _bst noattr))) ::
               (_t'25, (tptr (Tstruct _bst noattr))) ::
               (_t'24, (tptr (Tstruct _bst noattr))) ::
               (_t'23, (tptr (Tstruct _bst noattr))) :: (_t'22, tint) ::
               (_t'21, (tptr (Tstruct _bst noattr))) :: (_t'20, tint) ::
               (_t'19, (tptr (Tstruct _bst noattr))) ::
               (_t'18, (tptr (Tstruct _bst noattr))) ::
               (_t'17, (tptr (Tstruct _bst noattr))) ::
               (_t'16, (tptr (Tstruct _bst noattr))) ::
               (_t'15, (tptr (Tstruct _bst noattr))) ::
               (_t'14, (tptr (Tstruct _bst noattr))) ::
               (_t'13, (tptr (Tstruct _bst noattr))) ::
               (_t'12, (tptr (Tstruct _bst noattr))) ::
               (_t'11, (tptr (Tstruct _bst noattr))) ::
               (_t'10, (tptr (Tstruct _bst noattr))) ::
               (_t'9, (tptr (Tstruct _bst noattr))) ::
               (_t'8, (tptr (Tstruct _bst noattr))) :: (_t'7, tint) ::
               (_t'6, (tptr (Tstruct _bst noattr))) :: (_t'5, tint) ::
               (_t'4, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _parent
    (Ederef (Etempvar _parent_ptr (tptr (tptr (Tstruct _bst noattr))))
      (tptr (Tstruct _bst noattr))))
  (Sifthenelse (Eunop Onotbool
                 (Etempvar _parent (tptr (Tstruct _bst noattr))) tint)
    (Sreturn None)
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _parent (tptr (Tstruct _bst noattr)))
            (Tstruct _bst noattr)) _key tint))
      (Sifthenelse (Ebinop Oeq (Etempvar _key tint) (Etempvar _t'4 tint)
                     tint)
        (Ssequence
          (Sset _t'44
            (Efield
              (Ederef (Etempvar _parent (tptr (Tstruct _bst noattr)))
                (Tstruct _bst noattr)) _left (tptr (Tstruct _bst noattr))))
          (Sifthenelse (Etempvar _t'44 (tptr (Tstruct _bst noattr)))
            (Ssequence
              (Sset _t'47
                (Efield
                  (Ederef (Etempvar _parent (tptr (Tstruct _bst noattr)))
                    (Tstruct _bst noattr)) _right
                  (tptr (Tstruct _bst noattr))))
              (Sifthenelse (Etempvar _t'47 (tptr (Tstruct _bst noattr)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'1)
                      (Evar _pop_min (Tfunction
                                       (Tcons
                                         (tptr (tptr (Tstruct _bst noattr)))
                                         Tnil) (tptr (Tstruct _bst noattr))
                                       cc_default))
                      ((Eaddrof
                         (Efield
                           (Ederef
                             (Etempvar _parent (tptr (Tstruct _bst noattr)))
                             (Tstruct _bst noattr)) _right
                           (tptr (Tstruct _bst noattr)))
                         (tptr (tptr (Tstruct _bst noattr)))) :: nil))
                    (Sset _min (Etempvar _t'1 (tptr (Tstruct _bst noattr)))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'50
                        (Efield
                          (Ederef
                            (Etempvar _min (tptr (Tstruct _bst noattr)))
                            (Tstruct _bst noattr)) _key tint))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _parent (tptr (Tstruct _bst noattr)))
                            (Tstruct _bst noattr)) _key tint)
                        (Etempvar _t'50 tint)))
                    (Ssequence
                      (Ssequence
                        (Sset _t'49
                          (Efield
                            (Ederef
                              (Etempvar _min (tptr (Tstruct _bst noattr)))
                              (Tstruct _bst noattr)) _val tint))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _parent (tptr (Tstruct _bst noattr)))
                              (Tstruct _bst noattr)) _val tint)
                          (Etempvar _t'49 tint)))
                      (Scall None
                        (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil)
                                      tvoid cc_default))
                        ((Etempvar _min (tptr (Tstruct _bst noattr))) :: nil)))))
                (Ssequence
                  (Ssequence
                    (Sset _t'48
                      (Efield
                        (Ederef
                          (Etempvar _parent (tptr (Tstruct _bst noattr)))
                          (Tstruct _bst noattr)) _left
                        (tptr (Tstruct _bst noattr))))
                    (Sassign
                      (Ederef
                        (Etempvar _parent_ptr (tptr (tptr (Tstruct _bst noattr))))
                        (tptr (Tstruct _bst noattr)))
                      (Etempvar _t'48 (tptr (Tstruct _bst noattr)))))
                  (Scall None
                    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                  cc_default))
                    ((Etempvar _parent (tptr (Tstruct _bst noattr))) :: nil)))))
            (Ssequence
              (Sset _t'45
                (Efield
                  (Ederef (Etempvar _parent (tptr (Tstruct _bst noattr)))
                    (Tstruct _bst noattr)) _right
                  (tptr (Tstruct _bst noattr))))
              (Sifthenelse (Etempvar _t'45 (tptr (Tstruct _bst noattr)))
                (Ssequence
                  (Ssequence
                    (Sset _t'46
                      (Efield
                        (Ederef
                          (Etempvar _parent (tptr (Tstruct _bst noattr)))
                          (Tstruct _bst noattr)) _right
                        (tptr (Tstruct _bst noattr))))
                    (Sassign
                      (Ederef
                        (Etempvar _parent_ptr (tptr (tptr (Tstruct _bst noattr))))
                        (tptr (Tstruct _bst noattr)))
                      (Etempvar _t'46 (tptr (Tstruct _bst noattr)))))
                  (Scall None
                    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                  cc_default))
                    ((Etempvar _parent (tptr (Tstruct _bst noattr))) :: nil)))
                (Ssequence
                  (Scall None
                    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                  cc_default))
                    ((Etempvar _parent (tptr (Tstruct _bst noattr))) :: nil))
                  (Sassign
                    (Ederef
                      (Etempvar _parent_ptr (tptr (tptr (Tstruct _bst noattr))))
                      (tptr (Tstruct _bst noattr)))
                    (Ecast
                      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                      (tptr (Tstruct _bst noattr)))))))))
        (Sloop
          (Ssequence
            Sskip
            (Ssequence
              (Sset _t'5
                (Efield
                  (Ederef (Etempvar _parent (tptr (Tstruct _bst noattr)))
                    (Tstruct _bst noattr)) _key tint))
              (Sifthenelse (Ebinop Olt (Etempvar _key tint)
                             (Etempvar _t'5 tint) tint)
                (Ssequence
                  (Sset _t'25
                    (Efield
                      (Ederef (Etempvar _parent (tptr (Tstruct _bst noattr)))
                        (Tstruct _bst noattr)) _left
                      (tptr (Tstruct _bst noattr))))
                  (Sifthenelse (Eunop Onotbool
                                 (Etempvar _t'25 (tptr (Tstruct _bst noattr)))
                                 tint)
                    (Sreturn None)
                    (Ssequence
                      (Sset _t'26
                        (Efield
                          (Ederef
                            (Etempvar _parent (tptr (Tstruct _bst noattr)))
                            (Tstruct _bst noattr)) _left
                          (tptr (Tstruct _bst noattr))))
                      (Ssequence
                        (Sset _t'27
                          (Efield
                            (Ederef
                              (Etempvar _t'26 (tptr (Tstruct _bst noattr)))
                              (Tstruct _bst noattr)) _key tint))
                        (Sifthenelse (Ebinop Oeq (Etempvar _key tint)
                                       (Etempvar _t'27 tint) tint)
                          (Ssequence
                            (Sset _t'28
                              (Efield
                                (Ederef
                                  (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                  (Tstruct _bst noattr)) _left
                                (tptr (Tstruct _bst noattr))))
                            (Ssequence
                              (Sset _t'29
                                (Efield
                                  (Ederef
                                    (Etempvar _t'28 (tptr (Tstruct _bst noattr)))
                                    (Tstruct _bst noattr)) _left
                                  (tptr (Tstruct _bst noattr))))
                              (Sifthenelse (Etempvar _t'29 (tptr (Tstruct _bst noattr)))
                                (Ssequence
                                  (Sset _t'35
                                    (Efield
                                      (Ederef
                                        (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                        (Tstruct _bst noattr)) _left
                                      (tptr (Tstruct _bst noattr))))
                                  (Ssequence
                                    (Sset _t'36
                                      (Efield
                                        (Ederef
                                          (Etempvar _t'35 (tptr (Tstruct _bst noattr)))
                                          (Tstruct _bst noattr)) _right
                                        (tptr (Tstruct _bst noattr))))
                                    (Sifthenelse (Etempvar _t'36 (tptr (Tstruct _bst noattr)))
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'43
                                              (Efield
                                                (Ederef
                                                  (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                                  (Tstruct _bst noattr))
                                                _left
                                                (tptr (Tstruct _bst noattr))))
                                            (Scall (Some _t'2)
                                              (Evar _pop_min (Tfunction
                                                               (Tcons
                                                                 (tptr (tptr (Tstruct _bst noattr)))
                                                                 Tnil)
                                                               (tptr (Tstruct _bst noattr))
                                                               cc_default))
                                              ((Eaddrof
                                                 (Efield
                                                   (Ederef
                                                     (Etempvar _t'43 (tptr (Tstruct _bst noattr)))
                                                     (Tstruct _bst noattr))
                                                   _right
                                                   (tptr (Tstruct _bst noattr)))
                                                 (tptr (tptr (Tstruct _bst noattr)))) ::
                                               nil)))
                                          (Sset _min__1
                                            (Etempvar _t'2 (tptr (Tstruct _bst noattr)))))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'41
                                              (Efield
                                                (Ederef
                                                  (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                                  (Tstruct _bst noattr))
                                                _left
                                                (tptr (Tstruct _bst noattr))))
                                            (Ssequence
                                              (Sset _t'42
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _min__1 (tptr (Tstruct _bst noattr)))
                                                    (Tstruct _bst noattr))
                                                  _key tint))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _t'41 (tptr (Tstruct _bst noattr)))
                                                    (Tstruct _bst noattr))
                                                  _key tint)
                                                (Etempvar _t'42 tint))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'39
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                                    (Tstruct _bst noattr))
                                                  _left
                                                  (tptr (Tstruct _bst noattr))))
                                              (Ssequence
                                                (Sset _t'40
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _min__1 (tptr (Tstruct _bst noattr)))
                                                      (Tstruct _bst noattr))
                                                    _val tint))
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _t'39 (tptr (Tstruct _bst noattr)))
                                                      (Tstruct _bst noattr))
                                                    _val tint)
                                                  (Etempvar _t'40 tint))))
                                            (Ssequence
                                              (Scall None
                                                (Evar _free (Tfunction
                                                              (Tcons
                                                                (tptr tvoid)
                                                                Tnil) tvoid
                                                              cc_default))
                                                ((Etempvar _min__1 (tptr (Tstruct _bst noattr))) ::
                                                 nil))
                                              (Sreturn None)))))
                                      (Ssequence
                                        (Sset _del
                                          (Efield
                                            (Ederef
                                              (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                              (Tstruct _bst noattr)) _left
                                            (tptr (Tstruct _bst noattr))))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'37
                                              (Efield
                                                (Ederef
                                                  (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                                  (Tstruct _bst noattr))
                                                _left
                                                (tptr (Tstruct _bst noattr))))
                                            (Ssequence
                                              (Sset _t'38
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _t'37 (tptr (Tstruct _bst noattr)))
                                                    (Tstruct _bst noattr))
                                                  _left
                                                  (tptr (Tstruct _bst noattr))))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                                    (Tstruct _bst noattr))
                                                  _left
                                                  (tptr (Tstruct _bst noattr)))
                                                (Etempvar _t'38 (tptr (Tstruct _bst noattr))))))
                                          (Ssequence
                                            (Scall None
                                              (Evar _free (Tfunction
                                                            (Tcons
                                                              (tptr tvoid)
                                                              Tnil) tvoid
                                                            cc_default))
                                              ((Etempvar _del (tptr (Tstruct _bst noattr))) ::
                                               nil))
                                            (Sreturn None)))))))
                                (Ssequence
                                  (Sset _t'30
                                    (Efield
                                      (Ederef
                                        (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                        (Tstruct _bst noattr)) _left
                                      (tptr (Tstruct _bst noattr))))
                                  (Ssequence
                                    (Sset _t'31
                                      (Efield
                                        (Ederef
                                          (Etempvar _t'30 (tptr (Tstruct _bst noattr)))
                                          (Tstruct _bst noattr)) _right
                                        (tptr (Tstruct _bst noattr))))
                                    (Sifthenelse (Etempvar _t'31 (tptr (Tstruct _bst noattr)))
                                      (Ssequence
                                        (Sset _del__1
                                          (Efield
                                            (Ederef
                                              (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                              (Tstruct _bst noattr)) _left
                                            (tptr (Tstruct _bst noattr))))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'33
                                              (Efield
                                                (Ederef
                                                  (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                                  (Tstruct _bst noattr))
                                                _left
                                                (tptr (Tstruct _bst noattr))))
                                            (Ssequence
                                              (Sset _t'34
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _t'33 (tptr (Tstruct _bst noattr)))
                                                    (Tstruct _bst noattr))
                                                  _right
                                                  (tptr (Tstruct _bst noattr))))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                                    (Tstruct _bst noattr))
                                                  _left
                                                  (tptr (Tstruct _bst noattr)))
                                                (Etempvar _t'34 (tptr (Tstruct _bst noattr))))))
                                          (Ssequence
                                            (Scall None
                                              (Evar _free (Tfunction
                                                            (Tcons
                                                              (tptr tvoid)
                                                              Tnil) tvoid
                                                            cc_default))
                                              ((Etempvar _del__1 (tptr (Tstruct _bst noattr))) ::
                                               nil))
                                            (Sreturn None))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'32
                                            (Efield
                                              (Ederef
                                                (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                                (Tstruct _bst noattr)) _left
                                              (tptr (Tstruct _bst noattr))))
                                          (Scall None
                                            (Evar _free (Tfunction
                                                          (Tcons (tptr tvoid)
                                                            Tnil) tvoid
                                                          cc_default))
                                            ((Etempvar _t'32 (tptr (Tstruct _bst noattr))) ::
                                             nil)))
                                        (Ssequence
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                                (Tstruct _bst noattr)) _left
                                              (tptr (Tstruct _bst noattr)))
                                            (Ecast
                                              (Ecast
                                                (Econst_int (Int.repr 0) tint)
                                                (tptr tvoid))
                                              (tptr (Tstruct _bst noattr))))
                                          (Sreturn None)))))))))
                          (Sset _parent
                            (Efield
                              (Ederef
                                (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                (Tstruct _bst noattr)) _left
                              (tptr (Tstruct _bst noattr)))))))))
                (Ssequence
                  (Ssequence
                    (Sset _t'24
                      (Efield
                        (Ederef
                          (Etempvar _parent (tptr (Tstruct _bst noattr)))
                          (Tstruct _bst noattr)) _right
                        (tptr (Tstruct _bst noattr))))
                    (Sifthenelse (Eunop Onotbool
                                   (Etempvar _t'24 (tptr (Tstruct _bst noattr)))
                                   tint)
                      (Sreturn None)
                      Sskip))
                  (Ssequence
                    (Sset _t'6
                      (Efield
                        (Ederef
                          (Etempvar _parent (tptr (Tstruct _bst noattr)))
                          (Tstruct _bst noattr)) _right
                        (tptr (Tstruct _bst noattr))))
                    (Ssequence
                      (Sset _t'7
                        (Efield
                          (Ederef
                            (Etempvar _t'6 (tptr (Tstruct _bst noattr)))
                            (Tstruct _bst noattr)) _key tint))
                      (Sifthenelse (Ebinop Oeq (Etempvar _key tint)
                                     (Etempvar _t'7 tint) tint)
                        (Ssequence
                          (Sset _t'8
                            (Efield
                              (Ederef
                                (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                (Tstruct _bst noattr)) _right
                              (tptr (Tstruct _bst noattr))))
                          (Ssequence
                            (Sset _t'9
                              (Efield
                                (Ederef
                                  (Etempvar _t'8 (tptr (Tstruct _bst noattr)))
                                  (Tstruct _bst noattr)) _left
                                (tptr (Tstruct _bst noattr))))
                            (Sifthenelse (Etempvar _t'9 (tptr (Tstruct _bst noattr)))
                              (Ssequence
                                (Sset _t'15
                                  (Efield
                                    (Ederef
                                      (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                      (Tstruct _bst noattr)) _right
                                    (tptr (Tstruct _bst noattr))))
                                (Ssequence
                                  (Sset _t'16
                                    (Efield
                                      (Ederef
                                        (Etempvar _t'15 (tptr (Tstruct _bst noattr)))
                                        (Tstruct _bst noattr)) _right
                                      (tptr (Tstruct _bst noattr))))
                                  (Sifthenelse (Etempvar _t'16 (tptr (Tstruct _bst noattr)))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'23
                                            (Efield
                                              (Ederef
                                                (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                                (Tstruct _bst noattr)) _right
                                              (tptr (Tstruct _bst noattr))))
                                          (Scall (Some _t'3)
                                            (Evar _pop_min (Tfunction
                                                             (Tcons
                                                               (tptr (tptr (Tstruct _bst noattr)))
                                                               Tnil)
                                                             (tptr (Tstruct _bst noattr))
                                                             cc_default))
                                            ((Eaddrof
                                               (Efield
                                                 (Ederef
                                                   (Etempvar _t'23 (tptr (Tstruct _bst noattr)))
                                                   (Tstruct _bst noattr))
                                                 _right
                                                 (tptr (Tstruct _bst noattr)))
                                               (tptr (tptr (Tstruct _bst noattr)))) ::
                                             nil)))
                                        (Sset _min__2
                                          (Etempvar _t'3 (tptr (Tstruct _bst noattr)))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'21
                                            (Efield
                                              (Ederef
                                                (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                                (Tstruct _bst noattr)) _right
                                              (tptr (Tstruct _bst noattr))))
                                          (Ssequence
                                            (Sset _t'22
                                              (Efield
                                                (Ederef
                                                  (Etempvar _min__2 (tptr (Tstruct _bst noattr)))
                                                  (Tstruct _bst noattr)) _key
                                                tint))
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _t'21 (tptr (Tstruct _bst noattr)))
                                                  (Tstruct _bst noattr)) _key
                                                tint) (Etempvar _t'22 tint))))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'19
                                              (Efield
                                                (Ederef
                                                  (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                                  (Tstruct _bst noattr))
                                                _right
                                                (tptr (Tstruct _bst noattr))))
                                            (Ssequence
                                              (Sset _t'20
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _min__2 (tptr (Tstruct _bst noattr)))
                                                    (Tstruct _bst noattr))
                                                  _val tint))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _t'19 (tptr (Tstruct _bst noattr)))
                                                    (Tstruct _bst noattr))
                                                  _val tint)
                                                (Etempvar _t'20 tint))))
                                          (Ssequence
                                            (Scall None
                                              (Evar _free (Tfunction
                                                            (Tcons
                                                              (tptr tvoid)
                                                              Tnil) tvoid
                                                            cc_default))
                                              ((Etempvar _min__2 (tptr (Tstruct _bst noattr))) ::
                                               nil))
                                            (Sreturn None)))))
                                    (Ssequence
                                      (Sset _del__2
                                        (Efield
                                          (Ederef
                                            (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                            (Tstruct _bst noattr)) _right
                                          (tptr (Tstruct _bst noattr))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'17
                                            (Efield
                                              (Ederef
                                                (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                                (Tstruct _bst noattr)) _right
                                              (tptr (Tstruct _bst noattr))))
                                          (Ssequence
                                            (Sset _t'18
                                              (Efield
                                                (Ederef
                                                  (Etempvar _t'17 (tptr (Tstruct _bst noattr)))
                                                  (Tstruct _bst noattr))
                                                _left
                                                (tptr (Tstruct _bst noattr))))
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                                  (Tstruct _bst noattr))
                                                _right
                                                (tptr (Tstruct _bst noattr)))
                                              (Etempvar _t'18 (tptr (Tstruct _bst noattr))))))
                                        (Ssequence
                                          (Scall None
                                            (Evar _free (Tfunction
                                                          (Tcons (tptr tvoid)
                                                            Tnil) tvoid
                                                          cc_default))
                                            ((Etempvar _del__2 (tptr (Tstruct _bst noattr))) ::
                                             nil))
                                          (Sreturn None)))))))
                              (Ssequence
                                (Sset _t'10
                                  (Efield
                                    (Ederef
                                      (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                      (Tstruct _bst noattr)) _right
                                    (tptr (Tstruct _bst noattr))))
                                (Ssequence
                                  (Sset _t'11
                                    (Efield
                                      (Ederef
                                        (Etempvar _t'10 (tptr (Tstruct _bst noattr)))
                                        (Tstruct _bst noattr)) _right
                                      (tptr (Tstruct _bst noattr))))
                                  (Sifthenelse (Etempvar _t'11 (tptr (Tstruct _bst noattr)))
                                    (Ssequence
                                      (Sset _del__3
                                        (Efield
                                          (Ederef
                                            (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                            (Tstruct _bst noattr)) _right
                                          (tptr (Tstruct _bst noattr))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'13
                                            (Efield
                                              (Ederef
                                                (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                                (Tstruct _bst noattr)) _right
                                              (tptr (Tstruct _bst noattr))))
                                          (Ssequence
                                            (Sset _t'14
                                              (Efield
                                                (Ederef
                                                  (Etempvar _t'13 (tptr (Tstruct _bst noattr)))
                                                  (Tstruct _bst noattr))
                                                _right
                                                (tptr (Tstruct _bst noattr))))
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                                  (Tstruct _bst noattr))
                                                _right
                                                (tptr (Tstruct _bst noattr)))
                                              (Etempvar _t'14 (tptr (Tstruct _bst noattr))))))
                                        (Ssequence
                                          (Scall None
                                            (Evar _free (Tfunction
                                                          (Tcons (tptr tvoid)
                                                            Tnil) tvoid
                                                          cc_default))
                                            ((Etempvar _del__3 (tptr (Tstruct _bst noattr))) ::
                                             nil))
                                          (Sreturn None))))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'12
                                          (Efield
                                            (Ederef
                                              (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                              (Tstruct _bst noattr)) _right
                                            (tptr (Tstruct _bst noattr))))
                                        (Scall None
                                          (Evar _free (Tfunction
                                                        (Tcons (tptr tvoid)
                                                          Tnil) tvoid
                                                        cc_default))
                                          ((Etempvar _t'12 (tptr (Tstruct _bst noattr))) ::
                                           nil)))
                                      (Ssequence
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _parent (tptr (Tstruct _bst noattr)))
                                              (Tstruct _bst noattr)) _right
                                            (tptr (Tstruct _bst noattr)))
                                          (Ecast
                                            (Ecast
                                              (Econst_int (Int.repr 0) tint)
                                              (tptr tvoid))
                                            (tptr (Tstruct _bst noattr))))
                                        (Sreturn None)))))))))
                        (Sset _parent
                          (Efield
                            (Ederef
                              (Etempvar _parent (tptr (Tstruct _bst noattr)))
                              (Tstruct _bst noattr)) _right
                            (tptr (Tstruct _bst noattr)))))))))))
          Sskip)))))
|}.

Definition composites : list composite_definition :=
(Composite _bst Struct
   ((_key, tint) :: (_val, tint) :: (_left, (tptr (Tstruct _bst noattr))) ::
    (_right, (tptr (Tstruct _bst noattr))) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_new_bst, Gfun(Internal f_new_bst)) ::
 (_search_bst, Gfun(Internal f_search_bst)) ::
 (_insert_bst, Gfun(Internal f_insert_bst)) ::
 (_pop_min,
   Gfun(External (EF_external "pop_min"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr (tptr (Tstruct _bst noattr))) Tnil)
     (tptr (Tstruct _bst noattr)) cc_default)) ::
 (_delete_bst, Gfun(Internal f_delete_bst)) :: nil).

Definition public_idents : list ident :=
(_delete_bst :: _pop_min :: _insert_bst :: _search_bst :: _new_bst ::
 _free :: _malloc :: ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_fsqrt ::
 ___builtin_fabs :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: ___builtin_bswap64 :: ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


