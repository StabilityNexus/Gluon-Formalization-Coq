From StableCoinFormalization Require Export Datatypes.
From StableCoinFormalization Require Export HelperFunctions.
From StableCoinFormalization Require Export Functions.
From StableCoinFormalization Require Export HelperLemmas.
Require Export Lia.
Local Open Scope R_scope.
Module Theorem3.
    Import Datatypes.
    Import HelperFunctions.
    Import HelperLemmas.
    Import Functions.
    Import Lia.
    Theorem peg_robustness_during_market_crashes :
        forall
            (s1 s2 : State),
            get_stablecoins (s1.(stableCoinState).(reactorState)) > 0 /\
            reserve_ratio (s1.(stableCoinState)) > (1 / extract_value (qStar)) /\
            target_price (s1.(stableCoinState)) > 0 /\
            target_price (s2.(stableCoinState)) > 0 /\
            (get_stablecoins (s1.(stableCoinState).(reactorState)) / 
            get_basecoins (s1.(stableCoinState).(reactorState))) = 
            (get_stablecoins (s2.(stableCoinState).(reactorState)) / 
            get_basecoins (s2.(stableCoinState).(reactorState))) /\
            base_coin_price_crash (s1) (s2) <= 
            (reserve_ratio (s1.(stableCoinState)) - (1 / extract_value (qStar))) / 
            (reserve_ratio (s1.(stableCoinState)))
            ->
            stablecoin_price (s2.(stableCoinState)) = 
            target_price (s2.(stableCoinState)).
    Proof.
        intros. destruct s2 as [sc2 t2]. destruct sc2 as [rs2 e2]. 
        destruct rs2 as [b2 s2 r2]. unfold stablecoin_price. unfold fusion_ratio. 
        simpl. simpl in H.
        assert (Rmin (extract_value qStar) (s2 * e2 / b2) = (s2 * e2) / b2) as H1.
        {
            destruct s1 as [sc1 t1]. destruct sc1 as [rs1 e1]. 
            destruct rs1 as [b1 s1 r1].
            unfold base_coin_price_crash in H. unfold reserve_ratio in H.
            unfold fusion_ratio in H. unfold get_exchange_rate in H.
            unfold get_basecoins in H. simpl in H.
            destruct H as [H0 [H1 [H2 [H3 [H4 H5]]]]].
            destruct reactorstate_assumption with (b := b1) (r := r1) (s := s1) as [H7 [H8 H9]].
            rewrite Rmin_comm. apply Rmin_left.
            set (y1 := 1 / e1) in H5. set (y2 := 1 / e2) in H5.
            set (rr1 := (1 / Rmin (extract_value qStar) (s1 * e1 / b1))) in H5.
            assert (//Rmin (extract_value qStar) (s1 * e1 / b1) < //extract_value qStar) as H6.
            { 
                destruct qStar as [q HqStar].
                apply Rinv_lt_contravar.
                - apply Rmult_lt_0_compat.
                    * simpl. apply Rinv_0_lt_compat.
                    destruct HqStar. apply r.
                    * simpl. apply Rinv_0_lt_compat. apply Rmin_pos. destruct HqStar.
                    apply r. unfold Rdiv. apply Rmult_lt_0_compat. nra.
                    apply Rinv_0_lt_compat. apply H7.
                - simpl. simpl in H1. nra. 
            }
            rewrite Rinv_inv in H6. rewrite Rinv_inv in H6.
            assert (Rmin (extract_value qStar) (s1 * e1 / b1) = (s1 * e1 / b1)) as H10.
            {
                apply rmin_ab_lt_a_imp_b. apply H6.
            }
            destruct qStar as [q HqStar]. simpl. simpl in H6. simpl in H5. 
            simpl in H10. simpl in rr1. simpl in H1.
            assert (e2 <= q * rr1 * e1) as H11.
            { 
                apply Rmult_le_compat_r with (r := y1) in H5.
                unfold Rdiv in H5. rewrite Rmult_assoc in H5. rewrite Rinv_l in H5.
                rewrite Rmult_1_r in H5. rewrite Rmult_minus_distr_r in H5.
                rewrite Rinv_r in H5. rewrite Rmult_minus_distr_r in H5.
                rewrite Rmult_1_l in H5. 
                assert (y2 >= 1 * / q * / rr1 * y1) as H11.
                { nra. }
                assert (1 * / q * / rr1 * y1 = y1 / (q * rr1)) as H12.
                { rewrite Rdiv_mult_distr. nra. }
                rewrite H12 in H11.
                assert (1 / y2 <= (q * rr1) / y1) as H13.
                { 
                    rewrite Rdiv_1_l. rewrite <- Rinv_inv with (r := q * rr1 / y1). 
                    apply Rle_Rinv_depr.
                    - rewrite Rinv_div. apply Rdiv_lt_0_compat.
                        * unfold y1. rewrite Rdiv_1_l. apply Rinv_0_lt_compat. apply H2.
                        * apply Rmult_lt_0_compat. nra. unfold rr1. 
                        rewrite Rdiv_1_l. apply Rinv_0_lt_compat. rewrite H10.
                        apply Rdiv_lt_0_compat. nra. nra.
                    - unfold y2. rewrite Rdiv_1_l. apply Rinv_0_lt_compat. nra.
                    - rewrite Rinv_div. nra.
                }
                unfold y1 in H13. rewrite a_div_b_c_imp_a_mult_c_div_b in H13.
                rewrite Rdiv_1_r in H13. unfold y2 in H13. 
                rewrite a_div_b_c_imp_a_mult_c_div_b in H13. 
                rewrite Rdiv_1_r in H13.  rewrite Rmult_1_l in H13. apply H13.
                - unfold rr1. rewrite H10. rewrite a_div_b_c_imp_a_mult_c_div_b.
                rewrite Rmult_1_l.
                assert (b1 / (s1 * e1) > 0) as H11.
                { apply Rdiv_pos_pos. apply H7. nra. }
                nra. 
                - unfold y1. unfold Rdiv. assert (1 / e1 > 0) as H11.
                { apply Rdiv_pos_pos. nra. nra. } nra.
                - unfold y1. apply Rlt_le. apply Rdiv_pos_pos. nra. nra.                
            }
            unfold rr1 in H11. rewrite H10 in H11.
            rewrite Rmult_div_assoc in H11. rewrite Rmult_1_r in H11.
            assert (q / (s1 * e1 / b1) * e1 = (q * b1) / s1) as H12.
            {
                rewrite Rmult_comm. rewrite Rmult_div_assoc. 
                rewrite a_div_b_c_imp_a_mult_c_div_b. 
                rewrite Rmult_assoc with (r1 := e1). rewrite Rmult_comm.
                apply Rdiv_mult_r_r. nra.
            }
            rewrite H12 in H11. 
            apply Rmult_le_compat_r with (r := s1) in H11. unfold Rdiv in H11.
            rewrite Rmult_assoc with (r1 := q * b1) in H11. rewrite Rinv_l in H11.
            rewrite Rmult_1_r in H11. apply Rmult_le_compat_r with (r := / b1) in H11.
            rewrite Rmult_assoc with (r1 := q) in H11. rewrite Rinv_r in H11.
            rewrite Rmult_1_r in H11. unfold Rdiv in H4. rewrite Rmult_assoc in H11.
            rewrite H4 in H11. rewrite <- Rmult_assoc in H11. 
            rewrite Rmult_comm with (r1 := e2) in H11. unfold Rdiv. apply H11.
            nra. apply Rlt_le. apply Rinv_0_lt_compat. nra. nra. nra.
        }
        destruct reactorstate_assumption with (b := b2) (r := r2) (s := s2) as [H2 [H3 H4]].
        rewrite H1. unfold Rdiv. rewrite Rmult_assoc with (r1 := s2 * e2).
        rewrite Rmult_inv_l. rewrite Rmult_1_r.
        rewrite Rmult_comm. rewrite <- Rmult_assoc with (r1 := /s2).
        rewrite Rmult_inv_l. rewrite Rmult_1_l.
        - reflexivity.
        - nra.
        - nra.
    Qed.
End Theorem3.



