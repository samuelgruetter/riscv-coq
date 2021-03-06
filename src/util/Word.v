Require Export Coq.ZArith.BinIntDef.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.Eqdep_dec.
Require Import bbv.ZLib.
Require Import bbv.ZHints.
Require Import bbv.N_Z_nat_conversions.
Require bbv.Word.
Require Import riscv.util.ZBitOps.
Require Import riscv.util.prove_Zeq_bitwise.
Require Import riscv.util.Tactics.
Require Import riscv.util.div_mod_to_quot_rem.
Local Open Scope Z_scope.


(** The two axioms [uwordToZ_ZToWord] and [ZToWord_uwordToZ] fully specify the data type
    [word sz] with respect to its constructor [ZToWord] and its destructor [uwordToZ].
    Therefore, we will never have to unfold [ZToWord] or [uwordToZ] in the word library. *)
Module Type WORD.

  Parameter word: Z -> Set.

  Parameter ZToWord: forall (sz: Z) (x: Z), word sz.

  Parameter uwordToZ: forall {sz: Z} (w: word sz), Z.

  Axiom uwordToZ_ZToWord: forall sz n,
    uwordToZ (ZToWord sz n) = n mod 2 ^ sz.

  Axiom ZToWord_uwordToZ: forall {sz: Z} (a : word sz),
    ZToWord sz (uwordToZ a) = a.

End WORD.


Module Word(W: WORD).
  Export W.

  Section Derived.

    Context {sz: Z}.

    Lemma uwordToZ_inj: forall {a b: word sz},
        uwordToZ a = uwordToZ b -> a = b.
    Proof.
      intros.
      rewrite <- (ZToWord_uwordToZ a).
      rewrite <- (ZToWord_uwordToZ b).
      f_equal.
      assumption.
    Qed.

    Lemma mod_eq_ZToWord_eq: forall {a b: Z},
        a mod 2 ^ sz = b mod 2 ^ sz ->
        ZToWord sz a = ZToWord sz b.
    Proof.
      intros.
      apply uwordToZ_inj.
      rewrite? uwordToZ_ZToWord.
      assumption.
    Qed.

    Lemma ZToWord_eq_mod_eq: forall {a b: Z},
        ZToWord sz a = ZToWord sz b ->
        a mod 2 ^ sz = b mod 2 ^ sz.
    Proof.
      intros.
      rewrite <-? uwordToZ_ZToWord.
      f_equal.
      assumption.
    Qed.

    Lemma uwordToZ_mod: forall (a: word sz),
        uwordToZ a mod 2 ^ sz = uwordToZ a.
    Proof.
      intros.
      rewrite <- (ZToWord_uwordToZ a) at 2.
      rewrite uwordToZ_ZToWord.
      reflexivity.
    Qed.

    Lemma uwordToZ_ne: forall {a b: word sz},
        uwordToZ a <> uwordToZ b ->
        a <> b.
    Proof.
      intros a b E C. apply E. f_equal. assumption.
    Qed.

  End Derived.

  Definition wmsb{sz: Z}(a: word sz): bool := Z.testbit (uwordToZ a) (sz - 1).

  Definition swordToZ{sz: Z}(a: word sz): Z :=
    if wmsb a then uwordToZ a - 2 ^ sz else uwordToZ a.

  Definition wu_unop(f: Z -> Z)(sz: Z)(a: word sz): word sz :=
    ZToWord sz (f (uwordToZ a)).

  Definition wu_binop(f: Z -> Z -> Z)(sz: Z)(a b: word sz): word sz :=
    ZToWord sz (f (uwordToZ a) (uwordToZ b)).

  Definition wu_binop_t{T: Type}(f: Z -> Z -> T)(sz: Z)(a b: word sz): T :=
    f (uwordToZ a) (uwordToZ b).

  Definition ws_unop(f: Z -> Z)(sz: Z)(a: word sz): word sz :=
    ZToWord sz (f (swordToZ a)).

  Definition ws_binop(f: Z -> Z -> Z)(sz: Z)(a b: word sz): word sz :=
    ZToWord sz (f (swordToZ a) (swordToZ b)).

  Definition ws_binop_t{T: Type}(f: Z -> Z -> T)(sz: Z)(a b: word sz): T :=
    f (swordToZ a) (swordToZ b).

  Hint Unfold wmsb swordToZ
       wu_unop wu_binop wu_binop_t
       ws_unop ws_binop ws_binop_t
       proj1_sig
    : unf_word_all.


  Section ArithOps.

    Context {sz: Z}.

    Definition wopp := ws_unop Z.opp sz.

    Definition wadd := wu_binop Z.add sz.
    Definition wsub := wu_binop Z.sub sz.
    Definition wmul := wu_binop Z.mul sz.

    Definition wsadd := ws_binop Z.add sz.
    Definition wssub := ws_binop Z.sub sz.
    Definition wsmul := ws_binop Z.mul sz.

  End ArithOps.

  Hint Unfold wopp wadd wsub wmul wsadd wssub wsmul : unf_word_all.


  Ltac make_mod_nonzero :=
    let C := fresh in
    match goal with
    | |- context [_ mod ?m] =>
      assert (m = 0 \/ m <> 0) as C by omega;
      destruct C as [C | C];
      [ rewrite C in *; rewrite? Zmod_0_r; reflexivity | ]
    end.

  Ltac mod0_exists_quotient H :=
    apply Z.mod_divide in H;
    [ let k := fresh "k" in let E := fresh "E" in unfold Z.divide in H; destruct H as [k E] | ].

  Lemma mod_eq_from_diff: forall {a b m: Z},
      (a - b) mod m = 0 ->
      a mod m = b mod m.
  Proof.
    intros.
    make_mod_nonzero.
    mod0_exists_quotient H; [|assumption].
    replace a with (b + k * m) by omega.
    apply Z_mod_plus_full.
  Qed.

  Lemma mod_eq_to_diff: forall {a b m : Z},
      a mod m = b mod m ->
      (a - b) mod m = 0.
  Proof.
    intros.
    make_mod_nonzero.
    apply Z.mod_divide; [assumption|].
    unfold Z.divide.
    div_mod_to_quot_rem.
    subst a b r0.
    exists (q - q0).
    ring.
  Qed.

  Ltac prove_mod_0 :=
    match goal with
    | |- ?a mod ?m = 0 => ring_simplify a
    end;
    rewrite? Zplus_mod_idemp_l;
    rewrite? Zplus_mod_idemp_r;
    rewrite? Zminus_mod_idemp_l;
    rewrite? Zminus_mod_idemp_r;
    rewrite? Zmult_mod_idemp_l;
    rewrite? Zmult_mod_idemp_r;
    match goal with
    | |- ?a mod ?m = 0 => ring_simplify a
    end;
    rewrite? Z.pow_2_r;
    first
      (* base cases: *)
      [ apply Z_mod_mult
      | apply Z_mod_mult'
      | apply Z_mod_same_full
      | apply Zmod_0_l
      (* cases with recursion (the last two might turn a true goal into a false one): *)
      | apply Z_mod_zero_opp_full
      | apply add_mod_0
      | apply sub_mod_0
(* | match goal with
      | |- ?G => fail 1000 "failed to solve" G
      end *)
      ];
    [> prove_mod_0 .. ].

  Ltac word_destruct :=
    intuition idtac;
    repeat autounfold with unf_word_all in *;
    repeat match goal with
           | w: word ?sz |- _ =>
             pose proof (ZToWord_uwordToZ w);
             pose proof (uwordToZ_mod w);
             let w' := fresh w in forget (uwordToZ w) as w'; subst w
           end;
    rewrite? uwordToZ_ZToWord in *;
    repeat match goal with
           | H: (?x =? ?y) = true |- _ =>
             apply Z.eqb_eq in H; try subst x; try subst y
           | H: ZToWord _ ?x = ZToWord _ ?y |- _ =>
             apply ZToWord_eq_mod_eq in H; try subst x; try subst y
           end;
    repeat match goal with
           | |- context[if ?b then _ else _] => let E := fresh "E" in destruct b eqn: E
           end.

  Ltac word_eq_pre :=
    repeat match goal with
           | H: ?a mod ?m = ?b mod ?m |- _ =>
             apply mod_eq_to_diff in H;
             match type of H with
             | ?a mod ?m = 0 => ring_simplify a in H
             end
           end;
    apply mod_eq_ZToWord_eq;
    auto;
    try match goal with
        | H: ?b mod ?m = ?b |- _  = ?b => refine (eq_trans _ H)
        end;
    try match goal with
        | H: ?a mod ?m = ?a |- ?a = _  => refine (eq_trans (eq_sym H) _)
        end;
    rewrite? Zplus_mod_idemp_l;
    rewrite? Zplus_mod_idemp_r;
    rewrite? Zminus_mod_idemp_l;
    rewrite? Zminus_mod_idemp_r;
    rewrite? Zmult_mod_idemp_l;
    rewrite? Zmult_mod_idemp_r;
    apply mod_eq_from_diff.

  Ltac word_solver := word_destruct; word_eq_pre; prove_mod_0.


  Section ArithOpsEquiv.

    Context {sz: Z}.

    Lemma wadd_wsadd: forall a b: word sz,
        wadd a b = wsadd a b.
    Proof. word_solver. Qed.

    Lemma wsub_wssub: forall a b: word sz,
        wsub a b = wssub a b.
    Proof. word_solver. Qed.

    Lemma wmul_wsmul: forall a b: word sz,
        wmul a b = wsmul a b.
    Proof. word_solver. Qed.

  End ArithOpsEquiv.


  Section MoreOps.

    Context {sz: Z}.

    Definition wudiv  := wu_binop Z.div sz.
    Definition wuquot := wu_binop Z.quot sz.
    Definition wumod  := wu_binop Z.modulo sz.
    Definition wurem  := wu_binop Z.rem sz.

    Definition wsdiv  := ws_binop Z.div sz.
    Definition wsquot := ws_binop Z.quot sz.
    Definition wsmod  := ws_binop Z.modulo sz.
    Definition wsrem  := ws_binop Z.rem sz.

    Definition wor   := wu_binop Z.lor sz.
    Definition wand  := wu_binop Z.land sz.
    Definition wxor  := wu_binop Z.lxor sz.

    Definition weqb := wu_binop_t Z.eqb sz.

    Definition weq_dec(x y: word sz): {x = y} + {x <> y}.
      destruct (Z.eq_dec (uwordToZ x) (uwordToZ y)).
      - left. apply uwordToZ_inj. assumption.
      - right. apply uwordToZ_ne. assumption.
    Defined.

    Definition wuleb := wu_binop_t Z.leb sz.
    Definition wultb := wu_binop_t Z.ltb sz.
    Definition wugeb := wu_binop_t Z.geb sz.
    Definition wugtb := wu_binop_t Z.gtb sz.

    Definition wsleb := ws_binop_t Z.leb sz.
    Definition wsltb := ws_binop_t Z.ltb sz.
    Definition wsgeb := ws_binop_t Z.geb sz.
    Definition wsgtb := ws_binop_t Z.gtb sz.

    Definition wshiftl  := wu_binop Z.shiftl sz.
    Definition wshiftr  := wu_binop Z.shiftr sz.
    Definition wshiftra := ws_binop Z.shiftr sz.

  End MoreOps.

  Hint Unfold
       wudiv wuquot wumod wurem
       wsdiv wsquot wsmod wsrem
       wor wand wxor
       weqb
       wuleb wultb wugeb wugtb
       wsleb wsltb wsgeb wsgtb
       wshiftl wshiftr wshiftra
    : unf_word_all.


  Definition wucast{sz: Z}(sz': Z)(w: word sz): word sz' :=
    ZToWord sz' (uwordToZ w).

  Definition wscast{sz: Z}(sz': Z)(w: word sz): word sz' :=
    ZToWord sz' (swordToZ w).

  Definition wappend{sz1 sz2: Z}(w1: word sz1)(w2: word sz2): word (sz1 + sz2) :=
    ZToWord (sz1 + sz2) (Z.lor (Z.shiftl (uwordToZ w1) sz2) (uwordToZ w2)).

  Definition wsplit_lo(sz1 sz2: Z)(w: word (sz1 + sz2)): word sz2 :=
    wucast sz2 w.

  Definition wsplit_hi(sz1 sz2: Z)(w: word (sz1 + sz2)): word sz1 :=
    ZToWord sz1 (Z.shiftr (uwordToZ w) sz2).

  Definition lobits(sz: Z)(w: word (sz + sz)): word sz := wsplit_lo sz sz w.

  Definition hibits(sz: Z)(w: word (sz + sz)): word sz := wsplit_hi sz sz w.

  Hint Unfold wucast wscast wappend wsplit_lo wsplit_hi lobits hibits : unf_word_all.

  Ltac word_omega_pre :=
    repeat match goal with
           | n: Z |- _ =>
             let B := fresh in assert (0 < n) by omega;
                               unique pose proof (pow2_times2 n B)
           | _: context[2 ^ ?n] |- _ =>
             let B := fresh in assert (0 <= n) by omega;
                               unique pose proof (pow2_pos n B)
           | _: context[?a mod ?m] |- _ =>
             let B := fresh in assert (0 < m) by omega;
                               unique pose proof (Z.mod_pos_bound a m B)
           | H: ?a mod 2 ^ _ = ?a      |- _ => apply mod_pow2_same_bounds in H; [|omega]
           | H: Z.testbit _ _ = true   |- _ => apply testbit_true_nonneg in H; [|omega..]
           | H: Z.testbit _ _ = false  |- _ => apply testbit_false_nonneg in H; [|omega..]
           | H1: ?a <= ?b, H2: ?b < ?c  |- _ => unique pose proof (conj H1 H2)
           | H: - 2 ^ _ <= ?n < 2 ^ _   |- _ => unique pose proof (signed_bounds_to_sz_pos _ _ H)
           end.

  Ltac word_omega := word_omega_pre; omega.

  Ltac word_bitwise_pre :=
    apply mod_eq_ZToWord_eq;
    rewrite <-? Z.land_ones by omega;
    (repeat match goal with
            | H: ?a mod 2 ^ _ = ?a |- _ => apply mod_pow2_same_bounds in H; [|omega]
            end).

  Ltac word_bitwise := word_destruct; word_bitwise_pre; prove_Zeq_bitwise.

  Lemma wappend_split: forall sz1 sz2 (w : word (sz1 + sz2)),
      0 <= sz1 ->
      0 <= sz2 ->
      wappend (wsplit_hi sz1 sz2 w) (wsplit_lo sz1 sz2 w) = w.
  Proof. word_bitwise. Qed.

  Lemma wsplit_lo_wappend: forall {sz1 sz2} (w1: word sz1) (w2: word sz2),
      0 <= sz1 ->
      0 <= sz2 ->
      wsplit_lo sz1 sz2 (wappend w1 w2) = w2.
  Proof. word_bitwise. Qed.

  Lemma wsplit_hi_wappend: forall {sz1 sz2} (w1: word sz1) (w2: word sz2),
      0 <= sz1 ->
      0 <= sz2 ->
      wsplit_hi sz1 sz2 (wappend w1 w2) = w1.
  Proof. word_bitwise. Qed.

  Lemma wappend_inj: forall {sz1 sz2} (a : word sz1) (b : word sz2) (c : word sz1) (d : word sz2),
      0 <= sz1 ->
      0 <= sz2 ->
      wappend a b = wappend c d ->
      a = c /\ b = d.
  Proof.
    intros.
    pose proof (wsplit_lo_wappend a b H H0).
    pose proof (wsplit_hi_wappend a b H H0).
    pose proof (wsplit_lo_wappend c d H H0).
    pose proof (wsplit_hi_wappend c d H H0).
    split; congruence.
  Qed.

  Lemma word_ring: forall sz,
      ring_theory (ZToWord sz 0) (ZToWord sz 1) wadd wmul wsub wopp eq.
  Proof.
    intros. constructor; word_solver.
  Qed.

  Lemma word_ring_morph_Z: forall sz,
      ring_morph (ZToWord sz 0) (ZToWord sz 1) wadd  wmul  wsub  wopp  eq
                 0              1              Z.add Z.mul Z.sub Z.opp Z.eqb
                 (ZToWord sz).
  Proof.
    intros. constructor; word_solver.
  Qed.

  Lemma weqb_spec: forall {sz: Z} (a b : word sz),
      weqb a b = true <-> a = b.
  Proof.
    word_destruct.
    - reflexivity.
    - apply Z.eqb_eq; word_omega.
  Qed.

  Lemma weqb_true: forall {sz} (x y : word sz), weqb x y = true -> x = y.
  Proof.
    eapply @weqb_spec.
  Qed.

  Lemma weqb_eq: forall {sz} (a b: word sz), a = b -> weqb a b = true.
  Proof.
    eapply @weqb_spec.
  Qed.

  Lemma weqb_false: forall {sz} (a b: word sz), weqb a b = false -> a <> b.
  Proof.
    intros. destruct (weqb a b) eqn: E.
    - discriminate.
    - intro C. subst. rewrite weqb_eq in E; congruence.
  Qed.

  Lemma weqb_ne: forall {sz} (a b: word sz), a <> b -> weqb a b = false.
  Proof.
    intros. destruct (weqb a b) eqn: E.
    - apply weqb_true in E. contradiction.
    - reflexivity.
  Qed.

  Lemma swordToZ_bound: forall sz (a : word sz),
      0 < sz ->
      - 2 ^ (sz - 1) <= swordToZ a < 2 ^ (sz - 1).
  Proof. word_destruct; word_omega. Qed.

  Lemma uwordToZ_bound: forall sz (a : word sz),
      0 < sz ->
      0 <= uwordToZ a < 2 ^ sz.
  Proof. word_destruct; word_omega. Qed.

  Lemma swordToZ_ZToWord: forall sz n,
      - 2 ^ (sz - 1) <= n < 2 ^ (sz - 1) ->
      swordToZ (ZToWord sz n) = n.
  Proof.
    word_destruct; word_omega_pre;
      assert (sz = 1 \/ 1 < sz) as C by omega;
      (destruct C as [C | C];
       [subst sz;
        repeat match goal with
               | _: context[2 ^ ?x] |- _ =>
                 let r := eval cbv in (2 ^ x) in change (2 ^ x) with r in *
               end;
        assert (n = -1 \/ n = 0) as C by omega;
        destruct C; subst n; cbv in E; try reflexivity; congruence |]);
      match goal with
      | _: context[?a mod ?m] |- _ =>
        let B := fresh in
        assert (m <> 0) by omega;
          pose proof (Z.mod_eq a m B) as M
      end;
      assert (- 2 ^ (sz - 1) <= n <= 2 ^ (sz - 1) + 1) as B by omega;
      (apply (range_div_pos _ _ _ (2 ^ sz)) in B; [|omega]);
      assert (2 ^ (sz - 1) mod 2 ^ sz = 2 ^ (sz - 1)) by (apply Z.mod_small; omega);
      rewrite Z.div_opp_l_nz in B by omega;
      rewrite Z.div_small in B by omega;
      (rewrite (Z.div_small (2 ^ (sz - 1) + 1) (2 ^ sz)) in B;
       [ assert (n / 2 ^ sz = 0 \/ n / 2 ^ sz = -1) as R by omega;
         destruct R as [R | R]; rewrite R in M; omega
       | split; try omega;
         rewrite H4;
         pose proof (Z.pow_gt_1 2 (sz - 1));
         omega ]).
  Qed.

  Lemma ZToWord_swordToZ: forall sz (a : word sz),
      ZToWord sz (swordToZ a) = a.
  Proof. word_solver. Qed.

End Word.


(** Different ways to instantiate WORD: *)

(* Note: we don't use this because see below *)
Module SigmaWord <: WORD.

  Lemma sigma_canonicalize_eq: forall {A : Type},
    (forall x1 x2 : A, {x1 = x2} + {x1 <> x2}) ->
    forall (canonicalize: A -> A) (x1 x2: A) (p1: canonicalize x1 = x1) (p2: canonicalize x2 = x2),
      x1 = x2 ->
      exist (fun x => canonicalize x = x) x1 p1 = exist (fun x => canonicalize x = x) x2 p2.
  Proof.
    intros.
    subst x2.
    f_equal.
    apply (UIP_dec X p1 p2).
  Qed.

  Definition word(sz: Z) := { x: Z | x mod 2 ^ sz = x }.

  Definition ZToWord(sz: Z)(x: Z): word sz := exist _ (x mod 2 ^ sz) (Zmod_mod x (2 ^ sz)).

  Definition uwordToZ{sz: Z}: word sz -> Z := @proj1_sig Z (fun x => x mod 2 ^ sz = x).

  Lemma uwordToZ_ZToWord: forall {sz: Z} (n: Z),
      uwordToZ (ZToWord sz n) = n mod 2 ^ sz.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma ZToWord_uwordToZ: forall {sz: Z} (a : word sz),
      ZToWord sz (uwordToZ a) = a.
  Proof.
    intros. destruct a as [a Ma]. unfold ZToWord, uwordToZ.
    simpl.
    apply (sigma_canonicalize_eq Z.eq_dec).
    assumption.
  Qed.

  (* Prints a huge term, and is very slow, therefore this implementation is not usable
  Eval cbv in (ZToWord 4 3).
  *)
End SigmaWord.


(* Instead, we can just use bbv.Word: *)
Module BbvWord <: WORD.

  Definition word(sz: Z) := bbv.Word.word (Z.to_nat sz).

  (* Note: we do not reuse bbv.Word.ZToWord, because that would make the proof of
   uwordToZ_ZToWord below very hard *)
  Definition ZToWord(sz: Z)(x: Z): word sz :=
    bbv.Word.NToWord (Z.to_nat sz) (Z.to_N (x mod 2 ^ sz)).

  Definition uwordToZ{sz: Z}(w: word sz): Z := bbv.Word.uwordToZ w.

  Lemma neg_size: forall sz (a: word sz),
      sz < 0 ->
      a = Word.wzero (Z.to_nat sz).
  Proof.
    intros. unfold word in *.
    remember (Z.to_nat sz) as n.
    destruct a.
    - reflexivity.
    - exfalso. rewrite Z_to_nat_neg in Heqn by assumption. discriminate.
  Qed.

  Lemma uwordToZ_ZToWord: forall {sz: Z} (n: Z),
      uwordToZ (ZToWord sz n) = n mod 2 ^ sz.
  Proof.
    intros.
    unfold uwordToZ, ZToWord, bbv.Word.uwordToZ.
    assert (sz < 0 \/ 0 <= sz) as C by omega.
    destruct C as [C | C].
    - rewrite Z.pow_neg_r by assumption. rewrite Zmod_0_r.
      rewrite Z_to_nat_neg by omega. reflexivity.
    - pose proof (pow2_pos _ C).
      rewrite Word.wordToN_NToWord_2.
      + apply Z2N.id. apply Z.mod_pos_bound. assumption.
      + rewrite NatLib.pow2_N. change 2%nat with (Z.to_nat 2).
        rewrite <- Z2Nat.inj_pow by omega.
        rewrite Z_nat_N.
        pose proof (Z.mod_pos_bound n (2 ^ sz) H).
        apply Z2N.inj_lt; omega.
  Qed.

  Lemma ZToWord_uwordToZ: forall {sz: Z} (a : word sz),
      ZToWord sz (uwordToZ a) = a.
  Proof.
    intros.
    unfold uwordToZ, ZToWord, bbv.Word.uwordToZ.
    assert (sz < 0 \/ 0 <= sz) as C by omega.
    destruct C as [C | C].
    - rewrite Z.pow_neg_r by assumption. rewrite Zmod_0_r.
      rewrite neg_size by assumption.
      apply Word.NToWord_0.
    - rewrite Z2N.inj_mod.
      + rewrite N2Z.id.
        rewrite N.mod_small.
        * apply  Word.NToWord_wordToN.
        * pose proof (Word.wordToN_bound a) as P.
          rewrite NatLib.pow2_N in P. change 2%nat with (Z.to_nat 2) in P.
          rewrite <- Z2Nat.inj_pow in P by omega.
          rewrite Z_nat_N in P.
          exact P.
      + apply N2Z.is_nonneg.
      + apply pow2_pos. assumption.
  Qed.

  (* fast, as desired:
  Eval cbv in (ZToWord 64 (-42)).
  *)
End BbvWord.


(* The problems with SigmaWord are:
   - cbv will reduce its argument (P : A -> Prop) to huge terms
   - cbv will reduce its proof argument of type (P x) to possibly huge terms
   We can solve this by reimplementing sigma types by fixing the (P : A -> Prop) argument,
   and making sure proof terms always are just eq_refl, as follows: *)
Module RecordWord <: WORD.

  Record word_record{sz: Z} := Build_word {
    word_val: Z;
    word_mod: word_val mod 2 ^ sz = word_val
  }.

  Definition word: Z -> Set := @word_record.

  Definition minimize_eq_proof{A: Type}(eq_dec: forall (x y: A), {x = y} + {x <> y}){x y: A}
    (pf: x = y): x = y :=
    match eq_dec x y with
    | left p => p
    | right n => match n pf: False with end
    end.

  Definition ZToWord(sz: Z)(x: Z): word sz :=
    Build_word sz (x mod 2 ^ sz) (minimize_eq_proof Z.eq_dec (Zmod_mod x (2 ^ sz))).

  Definition uwordToZ{sz: Z}: word sz -> Z := word_val.

  Lemma uwordToZ_ZToWord: forall {sz: Z} (n: Z),
      uwordToZ (ZToWord sz n) = n mod 2 ^ sz.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma sigma_canonicalize_eq: forall {A : Type},
    (forall x1 x2 : A, {x1 = x2} + {x1 <> x2}) ->
    forall (canonicalize: A -> A) (x1 x2: A) (p1: canonicalize x1 = x1) (p2: canonicalize x2 = x2),
      x1 = x2 ->
      exist (fun x => canonicalize x = x) x1 p1 = exist (fun x => canonicalize x = x) x2 p2.
  Proof.
    intros.
    subst x2.
    f_equal.
    apply (UIP_dec X p1 p2).
  Qed.

  Lemma Build_word_eq: forall (sz x1 x2: Z) (p1: x1 mod 2 ^ sz = x1) (p2: x2 mod 2 ^ sz = x2),
      x1 = x2 ->
      Build_word sz x1 p1 = Build_word sz x2 p2.
  Proof.
    intros.
    subst x2.
    f_equal.
    apply UIP_dec.
    apply Z.eq_dec.
  Qed.

  Lemma ZToWord_uwordToZ: forall {sz: Z} (a : word sz),
      ZToWord sz (uwordToZ a) = a.
  Proof.
    intros. destruct a as [a Ma]. unfold ZToWord, uwordToZ.
    simpl.
    apply Build_word_eq.
    assumption.
  Qed.

  (* fast, as desired:
  Eval cbv in (ZToWord 64 (-42)).
  *)

End RecordWord.

Module Export WordLib := Word RecordWord.
