From Coq Require Import Reals Ring Classical.
Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _zz : R.
Definition _z := (rounding_float rndNE (53)%positive (-1074)%Z) _zz.
Variable _xx : R.
Definition _x := (rounding_float rndNE (53)%positive (-1074)%Z) _xx.
Definition r9 := (_z - _x)%R.
Definition _r := (rounding_float rndNE (53)%positive (-1074)%Z) r9.
Variable _kk : R.
Definition _k := (rounding_float rndNE (53)%positive (-1074)%Z) _kk.
Definition r7 := (_r * _k)%R.
Definition _m := (rounding_float rndNE (53)%positive (-1074)%Z) r7.
Definition r16 := Float1 0.
Definition r5 := (_m + r16)%R.
Definition _a := (rounding_float rndNE (53)%positive (-1074)%Z) r5.
Definition r3 := (_a + _x)%R.
Definition _y := (rounding_float rndNE (53)%positive (-1074)%Z) r3.
Definition r18 := (_k * r9)%R.
Definition _f := (_x + r18)%R.
Definition r1 := (_y - _f)%R.
Definition r22 := (_y - r3)%R.
Definition r23 := (_a - r5)%R.
Definition r21 := (r22 + r23)%R.
Definition r24 := (_m - r7)%R.
Definition r20 := (r21 + r24)%R.
Definition r26 := (_r - r9)%R.
Definition r25 := (_k * r26)%R.
Definition r19 := (r20 + r25)%R.
Lemma a1 : r1 = r19.
Proof.
 unfold r19, r25, r26, r20, r24, r21, r23, r22, r1, _f, r18, _y, r3, _a, r5, r16, _m, r7, _k, _r, r9, _x, _z.
 unfold Float1; cbn; ring.
Qed.
Lemma b1 : r1 = r19.
 apply a1.
Qed.
Definition r31 := Float1 (1).
Definition r30 := (r31 - _k)%R.
Definition r29 := (r30 * _x)%R.
Definition r32 := (_k * _z)%R.
Definition r28 := (r29 + r32)%R.
Definition r27 := (r28 + r1)%R.
Lemma a2 : _y = r27.
Proof.
 unfold r27, r28, r32, r29, r30, r31, r19, r25, r26, r20, r24, r21, r23, r22, r1, _f, r18, _y, r3, _a, r5, r16, _m, r7, _k, _r, r9, _x, _z.
 unfold Float1; cbn; ring.
Qed.
Lemma b2 : _y = r27.
 apply a2.
Qed.
Definition f1 := Float2 (-1) (0).
Definition f2 := Float2 (1) (0).
Definition i1 := makepairF f1 f2.
Definition p1 := BND _x i1. (* BND(x, [-1, 1]) *)
Definition f3 := Float2 (-1) (-1).
Definition f4 := Float2 (1) (-1).
Definition i2 := makepairF f3 f4.
Definition p2 := BND _z i2. (* BND(z, [-0.5, 0.5]) *)
Definition s3 := p1 /\ p2.
Definition f5 := Float2 (0) (0).
Definition i3 := makepairF f5 f2.
Definition p3 := BND _k i3. (* BND(k, [0, 1]) *)
Definition s2 := s3 /\ p3.
Definition f6 := Float2 (-1) (2).
Definition f7 := Float2 (1) (2).
Definition i4 := makepairF f6 f7.
Definition p4 := BND _r i4. (* BND(r, [-4, 4]) *)
Definition s8 := not p4.
Definition p5 := BND _m i4. (* BND(m, [-4, 4]) *)
Definition s9 := not p5.
Definition s7 := s8 \/ s9.
Definition p6 := BND _a i4. (* BND(a, [-4, 4]) *)
Definition s10 := not p6.
Definition s6 := s7 \/ s10.
Definition f8 := Float2 (-1) (1).
Definition f9 := Float2 (1) (1).
Definition i5 := makepairF f8 f9.
Definition p7 := BND _y i5. (* BND(y, [-2, 2]) *)
Definition s11 := not p7.
Definition s5 := s6 \/ s11.
Definition f10 := Float2 (-1) (-51).
Definition f11 := Float2 (1) (-51).
Definition i6 := makepairF f10 f11.
Definition p8 := BND r1 i6. (* BND(y - f, [-4.4409e-16, 4.4409e-16]) *)
Definition s12 := not p8.
Definition s4 := s5 \/ s12.
Definition s1 := s2 /\ s4.
Definition s13 := s11 \/ s12.
Definition s15 := s10 \/ s11.
Definition s14 := s15 \/ s12.
Definition s18 := s9 \/ s10.
Definition s17 := s18 \/ s11.
Definition s16 := s17 \/ s12.
Lemma l6 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f12 := Float2 (-3) (-1).
Definition f13 := Float2 (3) (-1).
Definition i7 := makepairF f12 f13.
Definition p9 := BND _r i7. (* BND(r, [-1.5, 1.5]) *)
Definition p10 := BND r9 i7. (* BND(z - x, [-1.5, 1.5]) *)
Lemma l11 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Lemma l10 : s1 -> s3.
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj1 h1).
Qed.
Lemma l9 : s1 -> p2 (* BND(z, [-0.5, 0.5]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Lemma l12 : s1 -> p1 (* BND(x, [-1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj1 h1).
Qed.
Lemma t1 : p2 -> p1 -> p10.
Proof.
 intros h0 h1.
 refine (sub _z _x i2 i1 i7 h0 h1 _) ; finalize.
Qed.
Lemma l8 : s1 -> p10 (* BND(z - x, [-1.5, 1.5]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 assert (h2 := l12 h0).
 apply t1. exact h1. exact h2.
Qed.
Lemma t2 : p10 -> p9.
Proof.
 intros h0.
 refine (float_round_ne _ _ r9 i7 i7 h0 _) ; finalize.
Qed.
Lemma l7 : s1 -> p9 (* BND(r, [-1.5, 1.5]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t2. exact h1.
Qed.
Lemma l5 : s1 -> s16.
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l7 h0).
 refine (simplify (Ttree false (Ttree false (Ttree false (Ttree false (Tatom false (Abnd 0%nat i4)) (Tatom false (Abnd 1%nat i4))) (Tatom false (Abnd 2%nat i4))) (Tatom false (Abnd 3%nat i5))) (Tatom false (Abnd 4%nat i6))) (Ttree false (Ttree false (Ttree false (Tatom false (Abnd 1%nat i4)) (Tatom false (Abnd 2%nat i4))) (Tatom false (Abnd 3%nat i5))) (Tatom false (Abnd 4%nat i6))) (Abnd 0%nat i7) (List.cons _r (List.cons _m (List.cons _a (List.cons _y (List.cons r1 List.nil))))) h2 h1 _) ; finalize.
Qed.
Definition p11 := BND _m i7. (* BND(m, [-1.5, 1.5]) *)
Definition p12 := BND r7 i7. (* BND(r * k, [-1.5, 1.5]) *)
Lemma l15 : s1 -> p3 (* BND(k, [0, 1]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj2 h1).
Qed.
Lemma t3 : p9 -> p3 -> p12.
Proof.
 intros h0 h1.
 refine (mul_op _r _k i7 i3 i7 h0 h1 _) ; finalize.
Qed.
Lemma l14 : s1 -> p12 (* BND(r * k, [-1.5, 1.5]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l15 h0).
 apply t3. exact h1. exact h2.
Qed.
Lemma t4 : p12 -> p11.
Proof.
 intros h0.
 refine (float_round_ne _ _ r7 i7 i7 h0 _) ; finalize.
Qed.
Lemma l13 : s1 -> p11 (* BND(m, [-1.5, 1.5]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 apply t4. exact h1.
Qed.
Lemma l4 : s1 -> s14.
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l13 h0).
 refine (simplify (Ttree false (Ttree false (Ttree false (Tatom false (Abnd 0%nat i4)) (Tatom false (Abnd 1%nat i4))) (Tatom false (Abnd 2%nat i5))) (Tatom false (Abnd 3%nat i6))) (Ttree false (Ttree false (Tatom false (Abnd 1%nat i4)) (Tatom false (Abnd 2%nat i5))) (Tatom false (Abnd 3%nat i6))) (Abnd 0%nat i7) (List.cons _m (List.cons _a (List.cons _y (List.cons r1 List.nil)))) h2 h1 _) ; finalize.
Qed.
Definition p13 := BND _a i7. (* BND(a, [-1.5, 1.5]) *)
Definition p14 := BND r5 i7. (* BND(m + 0, [-1.5, 1.5]) *)
Definition i8 := makepairF f5 f5.
Definition p15 := BND r16 i8. (* BND(0, [0, 0]) *)
Lemma t5 : p15.
Proof.
 refine (constant1 _ i8 _) ; finalize.
Qed.
Lemma l18 : s1 -> p15 (* BND(0, [0, 0]) *).
Proof.
 intros h0.
 apply t5.
Qed.
Lemma t6 : p11 -> p15 -> p14.
Proof.
 intros h0 h1.
 refine (add _m r16 i7 i8 i7 h0 h1 _) ; finalize.
Qed.
Lemma l17 : s1 -> p14 (* BND(m + 0, [-1.5, 1.5]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 assert (h2 := l18 h0).
 apply t6. exact h1. exact h2.
Qed.
Lemma t7 : p14 -> p13.
Proof.
 intros h0.
 refine (float_round_ne _ _ r5 i7 i7 h0 _) ; finalize.
Qed.
Lemma l16 : s1 -> p13 (* BND(a, [-1.5, 1.5]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 apply t7. exact h1.
Qed.
Lemma l3 : s1 -> s13.
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l16 h0).
 refine (simplify (Ttree false (Ttree false (Tatom false (Abnd 0%nat i4)) (Tatom false (Abnd 1%nat i5))) (Tatom false (Abnd 2%nat i6))) (Ttree false (Tatom false (Abnd 1%nat i5)) (Tatom false (Abnd 2%nat i6))) (Abnd 0%nat i7) (List.cons _a (List.cons _y (List.cons r1 List.nil))) h2 h1 _) ; finalize.
Qed.
Definition f14 := Float2 (-13510798882111493) (-53).
Definition f15 := Float2 (13510798882111493) (-53).
Definition i9 := makepairF f14 f15.
Definition p16 := BND _y i9. (* BND(y, [-1.50001, 1.50001]) *)
Definition p17 := _y = r27. (* EQL(y, (1 - k) * x + k * z + (y - f)) *)
Lemma t8 : p17.
Proof.
 refine (b2) ; finalize.
Qed.
Lemma l20 : s1 -> p17 (* EQL(y, (1 - k) * x + k * z + (y - f)) *).
Proof.
 intros h0.
 apply t8.
Qed.
Definition p18 := BND r27 i9. (* BND((1 - k) * x + k * z + (y - f), [-1.50001, 1.50001]) *)
Definition p19 := BND r28 i7. (* BND((1 - k) * x + k * z, [-1.5, 1.5]) *)
Definition p20 := BND r29 i1. (* BND((1 - k) * x, [-1, 1]) *)
Definition p21 := BND r30 i3. (* BND(1 - k, [-0, 1]) *)
Definition i10 := makepairF f2 f2.
Definition p22 := BND r31 i10. (* BND(1, [1, 1]) *)
Lemma t9 : p22.
Proof.
 refine (constant1 _ i10 _) ; finalize.
Qed.
Lemma l25 : s1 -> p22 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t9.
Qed.
Lemma t10 : p22 -> p3 -> p21.
Proof.
 intros h0 h1.
 refine (sub r31 _k i10 i3 i3 h0 h1 _) ; finalize.
Qed.
Lemma l24 : s1 -> p21 (* BND(1 - k, [-0, 1]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 assert (h2 := l15 h0).
 apply t10. exact h1. exact h2.
Qed.
Lemma t11 : p21 -> p1 -> p20.
Proof.
 intros h0 h1.
 refine (mul_po r30 _x i3 i1 i1 h0 h1 _) ; finalize.
Qed.
Lemma l23 : s1 -> p20 (* BND((1 - k) * x, [-1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l12 h0).
 apply t11. exact h1. exact h2.
Qed.
Definition p23 := BND r32 i2. (* BND(k * z, [-0.5, 0.5]) *)
Lemma t12 : p3 -> p2 -> p23.
Proof.
 intros h0 h1.
 refine (mul_po _k _z i3 i2 i2 h0 h1 _) ; finalize.
Qed.
Lemma l26 : s1 -> p23 (* BND(k * z, [-0.5, 0.5]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 assert (h2 := l9 h0).
 apply t12. exact h1. exact h2.
Qed.
Lemma t13 : p20 -> p23 -> p19.
Proof.
 intros h0 h1.
 refine (add r29 r32 i1 i2 i7 h0 h1 _) ; finalize.
Qed.
Lemma l22 : s1 -> p19 (* BND((1 - k) * x + k * z, [-1.5, 1.5]) *).
Proof.
 intros h0.
 assert (h1 := l23 h0).
 assert (h2 := l26 h0).
 apply t13. exact h1. exact h2.
Qed.
Definition f16 := Float2 (-5) (-53).
Definition f17 := Float2 (5) (-53).
Definition i11 := makepairF f16 f17.
Definition p24 := BND r1 i11. (* BND(y - f, [-5.55112e-16, 5.55112e-16]) *)
Definition p25 := r1 = r19. (* EQL(y - f, y - (a + x) + (a - (m + 0)) + (m - r * k) + k * (r - (z - x))) *)
Lemma t14 : p25.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l28 : s1 -> p25 (* EQL(y - f, y - (a + x) + (a - (m + 0)) + (m - r * k) + k * (r - (z - x))) *).
Proof.
 intros h0.
 apply t14.
Qed.
Definition p26 := BND r19 i11. (* BND(y - (a + x) + (a - (m + 0)) + (m - r * k) + k * (r - (z - x)), [-5.55112e-16, 5.55112e-16]) *)
Definition p27 := BND r20 i6. (* BND(y - (a + x) + (a - (m + 0)) + (m - r * k), [-4.4409e-16, 4.4409e-16]) *)
Definition f18 := Float2 (-3) (-53).
Definition f19 := Float2 (3) (-53).
Definition i12 := makepairF f18 f19.
Definition p28 := BND r21 i12. (* BND(y - (a + x) + (a - (m + 0)), [-3.33067e-16, 3.33067e-16]) *)
Definition f20 := Float2 (-1) (-52).
Definition f21 := Float2 (1) (-52).
Definition i13 := makepairF f20 f21.
Definition p29 := BND r22 i13. (* BND(y - (a + x), [-2.22045e-16, 2.22045e-16]) *)
Definition i14 := makepairF f5 f7.
Definition p30 := ABS r3 i14. (* ABS(a + x, [0, 4]) *)
Definition p31 := BND r3 i4. (* BND(a + x, [-4, 4]) *)
Definition p32 := BND _a i5. (* BND(a, [-2, 2]) *)
Lemma t15 : p32 -> p1 -> p31.
Proof.
 intros h0 h1.
 refine (add _a _x i5 i1 i4 h0 h1 _) ; finalize.
Qed.
Lemma l34 : s1 -> p31 (* BND(a + x, [-4, 4]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l12 h0).
 apply t15. refine (subset _a i7 i5 h1 _) ; finalize. exact h2.
Qed.
Lemma t16 : p31 -> p30.
Proof.
 intros h0.
 refine (abs_of_bnd_o r3 i4 i14 h0 _) ; finalize.
Qed.
Lemma l33 : s1 -> p30 (* ABS(a + x, [0, 4]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 apply t16. exact h1.
Qed.
Lemma t17 : p30 -> p29.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r3 i14 i13 h0 _) ; finalize.
Qed.
Lemma l32 : s1 -> p29 (* BND(y - (a + x), [-2.22045e-16, 2.22045e-16]) *).
Proof.
 intros h0.
 assert (h1 := l33 h0).
 apply t17. exact h1.
Qed.
Definition f22 := Float2 (-1) (-53).
Definition f23 := Float2 (1) (-53).
Definition i15 := makepairF f22 f23.
Definition p33 := BND r23 i15. (* BND(a - (m + 0), [-1.11023e-16, 1.11023e-16]) *)
Definition i16 := makepairF f5 f9.
Definition p34 := ABS r5 i16. (* ABS(m + 0, [0, 2]) *)
Definition p35 := BND r5 i5. (* BND(m + 0, [-2, 2]) *)
Lemma t18 : p35 -> p34.
Proof.
 intros h0.
 refine (abs_of_bnd_o r5 i5 i16 h0 _) ; finalize.
Qed.
Lemma l36 : s1 -> p34 (* ABS(m + 0, [0, 2]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 apply t18. refine (subset r5 i7 i5 h1 _) ; finalize.
Qed.
Lemma t19 : p34 -> p33.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r5 i16 i15 h0 _) ; finalize.
Qed.
Lemma l35 : s1 -> p33 (* BND(a - (m + 0), [-1.11023e-16, 1.11023e-16]) *).
Proof.
 intros h0.
 assert (h1 := l36 h0).
 apply t19. exact h1.
Qed.
Lemma t20 : p29 -> p33 -> p28.
Proof.
 intros h0 h1.
 refine (add r22 r23 i13 i15 i12 h0 h1 _) ; finalize.
Qed.
Lemma l31 : s1 -> p28 (* BND(y - (a + x) + (a - (m + 0)), [-3.33067e-16, 3.33067e-16]) *).
Proof.
 intros h0.
 assert (h1 := l32 h0).
 assert (h2 := l35 h0).
 apply t20. exact h1. exact h2.
Qed.
Definition p36 := BND r24 i15. (* BND(m - r * k, [-1.11023e-16, 1.11023e-16]) *)
Definition p37 := ABS r7 i16. (* ABS(r * k, [0, 2]) *)
Definition p38 := BND r7 i5. (* BND(r * k, [-2, 2]) *)
Lemma t21 : p38 -> p37.
Proof.
 intros h0.
 refine (abs_of_bnd_o r7 i5 i16 h0 _) ; finalize.
Qed.
Lemma l38 : s1 -> p37 (* ABS(r * k, [0, 2]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 apply t21. refine (subset r7 i7 i5 h1 _) ; finalize.
Qed.
Lemma t22 : p37 -> p36.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r7 i16 i15 h0 _) ; finalize.
Qed.
Lemma l37 : s1 -> p36 (* BND(m - r * k, [-1.11023e-16, 1.11023e-16]) *).
Proof.
 intros h0.
 assert (h1 := l38 h0).
 apply t22. exact h1.
Qed.
Lemma t23 : p28 -> p36 -> p27.
Proof.
 intros h0 h1.
 refine (add r21 r24 i12 i15 i6 h0 h1 _) ; finalize.
Qed.
Lemma l30 : s1 -> p27 (* BND(y - (a + x) + (a - (m + 0)) + (m - r * k), [-4.4409e-16, 4.4409e-16]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l37 h0).
 apply t23. exact h1. exact h2.
Qed.
Definition p39 := BND r25 i15. (* BND(k * (r - (z - x)), [-1.11023e-16, 1.11023e-16]) *)
Definition p40 := BND r26 i15. (* BND(r - (z - x), [-1.11023e-16, 1.11023e-16]) *)
Definition p41 := ABS r9 i16. (* ABS(z - x, [0, 2]) *)
Definition p42 := BND r9 i5. (* BND(z - x, [-2, 2]) *)
Lemma t24 : p42 -> p41.
Proof.
 intros h0.
 refine (abs_of_bnd_o r9 i5 i16 h0 _) ; finalize.
Qed.
Lemma l41 : s1 -> p41 (* ABS(z - x, [0, 2]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t24. refine (subset r9 i7 i5 h1 _) ; finalize.
Qed.
Lemma t25 : p41 -> p40.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r9 i16 i15 h0 _) ; finalize.
Qed.
Lemma l40 : s1 -> p40 (* BND(r - (z - x), [-1.11023e-16, 1.11023e-16]) *).
Proof.
 intros h0.
 assert (h1 := l41 h0).
 apply t25. exact h1.
Qed.
Lemma t26 : p3 -> p40 -> p39.
Proof.
 intros h0 h1.
 refine (mul_po _k r26 i3 i15 i15 h0 h1 _) ; finalize.
Qed.
Lemma l39 : s1 -> p39 (* BND(k * (r - (z - x)), [-1.11023e-16, 1.11023e-16]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 assert (h2 := l40 h0).
 apply t26. exact h1. exact h2.
Qed.
Lemma t27 : p27 -> p39 -> p26.
Proof.
 intros h0 h1.
 refine (add r20 r25 i6 i15 i11 h0 h1 _) ; finalize.
Qed.
Lemma l29 : s1 -> p26 (* BND(y - (a + x) + (a - (m + 0)) + (m - r * k) + k * (r - (z - x)), [-5.55112e-16, 5.55112e-16]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 assert (h2 := l39 h0).
 apply t27. exact h1. exact h2.
Qed.
Lemma t28 : p25 -> p26 -> p24.
Proof.
 intros h0 h1.
 refine (bnd_rewrite r1 r19 i11 h0 h1) ; finalize.
Qed.
Lemma l27 : s1 -> p24 (* BND(y - f, [-5.55112e-16, 5.55112e-16]) *).
Proof.
 intros h0.
 assert (h1 := l28 h0).
 assert (h2 := l29 h0).
 apply t28. exact h1. exact h2.
Qed.
Lemma t29 : p19 -> p24 -> p18.
Proof.
 intros h0 h1.
 refine (add r28 r1 i7 i11 i9 h0 h1 _) ; finalize.
Qed.
Lemma l21 : s1 -> p18 (* BND((1 - k) * x + k * z + (y - f), [-1.50001, 1.50001]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l27 h0).
 apply t29. exact h1. exact h2.
Qed.
Lemma t30 : p17 -> p18 -> p16.
Proof.
 intros h0 h1.
 refine (bnd_rewrite _y r27 i9 h0 h1) ; finalize.
Qed.
Lemma l19 : s1 -> p16 (* BND(y, [-1.50001, 1.50001]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l21 h0).
 apply t30. exact h1. exact h2.
Qed.
Lemma l2 : s1 -> s12.
Proof.
 intros h0.
 assert (h1 := l3 h0).
 assert (h2 := l19 h0).
 refine (simplify (Ttree false (Tatom false (Abnd 0%nat i5)) (Tatom false (Abnd 1%nat i6))) (Tatom false (Abnd 1%nat i6)) (Abnd 0%nat i9) (List.cons _y (List.cons r1 List.nil)) h2 h1 _) ; finalize.
Qed.
Definition p43 := BND r19 i6. (* BND(y - (a + x) + (a - (m + 0)) + (m - r * k) + k * (r - (z - x)), [-4.4409e-16, 4.4409e-16]) *)
Definition p44 := BND r20 i12. (* BND(y - (a + x) + (a - (m + 0)) + (m - r * k), [-3.33067e-16, 3.33067e-16]) *)
Definition p45 := BND r21 i13. (* BND(y - (a + x) + (a - (m + 0)), [-2.22045e-16, 2.22045e-16]) *)
Definition p46 := BND r22 i15. (* BND(y - (a + x), [-1.11023e-16, 1.11023e-16]) *)
Definition f24 := Float2 (7) (-2).
Definition i17 := makepairF f5 f24.
Definition p47 := ABS _y i17. (* ABS(y, [0, 1.75]) *)
Definition f25 := Float2 (-7) (-2).
Definition i18 := makepairF f25 f24.
Definition p48 := BND _y i18. (* BND(y, [-1.75, 1.75]) *)
Lemma t31 : p48 -> p47.
Proof.
 intros h0.
 refine (abs_of_bnd_o _y i18 i17 h0 _) ; finalize.
Qed.
Lemma l47 : s1 -> p47 (* ABS(y, [0, 1.75]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 apply t31. refine (subset _y i9 i18 h1 _) ; finalize.
Qed.
Lemma t32 : p47 -> p46.
Proof.
 intros h0.
 refine (float_absolute_inv_ne _ _ _ i17 i15 h0 _) ; finalize.
Qed.
Lemma l46 : s1 -> p46 (* BND(y - (a + x), [-1.11023e-16, 1.11023e-16]) *).
Proof.
 intros h0.
 assert (h1 := l47 h0).
 apply t32. exact h1.
Qed.
Lemma t33 : p46 -> p33 -> p45.
Proof.
 intros h0 h1.
 refine (add r22 r23 i15 i15 i13 h0 h1 _) ; finalize.
Qed.
Lemma l45 : s1 -> p45 (* BND(y - (a + x) + (a - (m + 0)), [-2.22045e-16, 2.22045e-16]) *).
Proof.
 intros h0.
 assert (h1 := l46 h0).
 assert (h2 := l35 h0).
 apply t33. exact h1. exact h2.
Qed.
Lemma t34 : p45 -> p36 -> p44.
Proof.
 intros h0 h1.
 refine (add r21 r24 i13 i15 i12 h0 h1 _) ; finalize.
Qed.
Lemma l44 : s1 -> p44 (* BND(y - (a + x) + (a - (m + 0)) + (m - r * k), [-3.33067e-16, 3.33067e-16]) *).
Proof.
 intros h0.
 assert (h1 := l45 h0).
 assert (h2 := l37 h0).
 apply t34. exact h1. exact h2.
Qed.
Lemma t35 : p44 -> p39 -> p43.
Proof.
 intros h0 h1.
 refine (add r20 r25 i12 i15 i6 h0 h1 _) ; finalize.
Qed.
Lemma l43 : s1 -> p43 (* BND(y - (a + x) + (a - (m + 0)) + (m - r * k) + k * (r - (z - x)), [-4.4409e-16, 4.4409e-16]) *).
Proof.
 intros h0.
 assert (h1 := l44 h0).
 assert (h2 := l39 h0).
 apply t35. exact h1. exact h2.
Qed.
Lemma t36 : p25 -> p43 -> p8.
Proof.
 intros h0 h1.
 refine (bnd_rewrite r1 r19 i6 h0 h1) ; finalize.
Qed.
Lemma l42 : s1 -> p8 (* BND(y - f, [-4.4409e-16, 4.4409e-16]) *).
Proof.
 intros h0.
 assert (h1 := l28 h0).
 assert (h2 := l43 h0).
 apply t36. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l42 h0).
 refine (simplify (Tatom false (Abnd 0%nat i6)) Tfalse (Abnd 0%nat i6) (List.cons r1 List.nil) h2 h1 _) ; finalize.
Qed.
Theorem mean_update_contract : s2 -> p4 /\ p5 /\ p6 /\ p7 /\ p8.
Proof.
 intro H.
 assert (H4 : p4) by (apply NNPP; intro Bad; apply l1; unfold s1, s4, s5, s6, s7, s8, s9, s10, s11, s12; tauto).
 assert (H5 : p5) by (apply NNPP; intro Bad; apply l1; unfold s1, s4, s5, s6, s7, s8, s9, s10, s11, s12; tauto).
 assert (H6 : p6) by (apply NNPP; intro Bad; apply l1; unfold s1, s4, s5, s6, s7, s8, s9, s10, s11, s12; tauto).
 assert (H7 : p7) by (apply NNPP; intro Bad; apply l1; unfold s1, s4, s5, s6, s7, s8, s9, s10, s11, s12; tauto).
 assert (H8 : p8) by (apply NNPP; intro Bad; apply l1; unfold s1, s4, s5, s6, s7, s8, s9, s10, s11, s12; tauto).
 exact (conj H4 (conj H5 (conj H6 (conj H7 H8)))).
Qed.
End Generated_by_Gappa.
