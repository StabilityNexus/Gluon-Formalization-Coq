From StableCoinFormalization Require Export Datatypes.
From StableCoinFormalization Require Export HelperFunctions.
From StableCoinFormalization Require Export Functions.
From StableCoinFormalization Require Export HelperLemmas.
From StableCoinFormalization Require Export FunctionProofs.
Require Export Lia.
Local Open Scope R_scope.
Module Theorem5.
    Import Datatypes.
    Import HelperFunctions.
    Import HelperLemmas.
    Import FunctionProofs.
    Import Functions.
    Import Lia.

    Definition is_depeg (sCS : StableCoinState) : Prop :=
        fusion_ratio (sCS) = extract_value (qStar).
    

    Theorem insolvency :
        forall (s1 s2 : State) (e : Event) (t : Timestamp),
            is_valid_state (s1) /\ is_valid_state (s2) /\
            s2 = execute (s1) (e) (t) /\
            target_price (s1.(stableCoinState)) = target_price (s2.(stableCoinState)) /\
            (is_depeg (s1.(stableCoinState)) -> forall x, e <> BetaDecayNegEvent x) ->
            reservecoin_price (s2.(stableCoinState)) >= reservecoin_price (s1.(stableCoinState)).
    Proof.
        intros. destruct H as [H1 [H2 [H3 [H4 H5]]]]. 
        unfold reservecoin_price. simpl. destruct e eqn:E.
        (* Fission Case *)
        - unfold execute in H3. unfold fission_reaction in H3.
        rewrite fission_output_alt with 
        (sCS := stableCoinState s1) (bC := baseCoins0) in H3.
        simpl in H3. rewrite H3. 
        destruct s1 as [[[oldBC oldSC oldRC] oldER] oldT].
        destruct s2 as [[[newBC newSC newRC] newER] newT].
        unfold fusion_ratio. unfold get_stablecoins. unfold get_basecoins. unfold get_reservecoins.
        simpl.
        unfold fission_output in H3. unfold stablecoin_price in H3. 
        unfold reservecoin_price in H3. unfold get_basecoins in H3. 
        unfold get_reservecoins in H3. unfold get_stablecoins in H3. 
        unfold fusion_ratio in H3. simpl in H3. simpl. 
        set (f' := Rmin (extract_value qStar) ((oldSC + baseCoins0 * (1 - extract_value fissionFee) * oldSC / oldBC) * oldER / (oldBC + baseCoins0))).
        set (f := Rmin (extract_value qStar) (oldSC * oldER / oldBC)).
        assert 
        (
            (1 - f') * (oldBC + baseCoins0) / (oldRC + baseCoins0 * (1 - extract_value fissionFee) * oldRC / oldBC) = 
            ((1 - f') * oldBC * ((1 + (baseCoins0 / oldBC)) / (1 + (((1 - extract_value fissionFee) * baseCoins0) / (oldBC))))) / (oldRC)
        ) as H6.
        {
            rewrite Rmult_div_swap with 
            (r1 := (1 - f') * oldBC) 
            (r2 := ((1 + baseCoins0 / oldBC) /
            (1 +
             (1 - extract_value fissionFee) *
             baseCoins0 / oldBC)))
            (r3 := oldRC).
            rewrite a_div_b_mult_c_div_d_imp_a_mult_c_div_b_mult_d with
            (a := (1 - f') * oldBC)
            (b := oldRC)
            (c := (1 + baseCoins0 / oldBC)).
            rewrite Rmult_assoc with
            (r1 := 1 - f')
            (r2 := oldBC)
            (r3 := (1 + baseCoins0 / oldBC)).
            rewrite Rmult_plus_distr_l with
            (r1 := oldBC)
            (r2 := 1)
            (r3 := baseCoins0 / oldBC).
            rewrite Rmult_1_r.
            rewrite a_mult_b_div_a_eq_b with
            (a := oldBC)
            (b := baseCoins0).
            rewrite Rmult_plus_distr_l with
            (r1 := oldRC)
            (r2 := 1)
            (r3 := (1 - extract_value fissionFee) *
            baseCoins0 / oldBC).
            rewrite Rmult_1_r.
            rewrite Rmult_div_assoc with
            (r1 := oldRC)
            (r2 := (1 - extract_value fissionFee) *
            baseCoins0)
            (r3 := oldBC).
            rewrite Rmult_comm with
            (r1 := (1 - extract_value fissionFee))
            (r2 := baseCoins0).
            rewrite <- Rmult_assoc with
            (r1 := oldRC)
            (r2 := baseCoins0)
            (r3 := 1 - extract_value fissionFee).
            rewrite Rmult_comm with
            (r1 := oldRC)
            (r2 := baseCoins0).
            rewrite Rmult_assoc with
            (r1 := baseCoins0)
            (r2 := oldRC)
            (r3 := 1 - extract_value fissionFee).
            rewrite Rmult_comm with
            (r1 := oldRC)
            (r2 := 1 - extract_value fissionFee).
            rewrite Rmult_assoc with
            (r1 := baseCoins0)
            (r2 := 1 - extract_value fissionFee)
            (r3 := oldRC). reflexivity.
            destruct reactorstate_assumption with 
            (b := oldBC) 
            (r := oldRC) 
            (s := oldSC) as [H7 [H8 H9]].
            nra.    
        }
        rewrite H6.
        set (alpha := ((1 + baseCoins0 / oldBC) / (1 + (1 - extract_value fissionFee) * baseCoins0 / oldBC))).
        assert (alpha > 1) as H7.
        {
            unfold alpha. apply division_greater_than_one.
            - apply Rplus_gt_compat_l with (r := 1). unfold Rdiv.
            apply Rmult_gt_compat_r with (r := / oldBC).
            destruct reactorstate_assumption with 
            (b := oldBC) 
            (r := oldRC) 
            (s := oldSC) as [H7 [H8 H9]]. apply Rinv_pos. apply H7.
            rewrite <- Rmult_1_l with (r := baseCoins0) at 1.
            apply Rmult_gt_compat_r with (r := baseCoins0).
            destruct reactorstate_assumption with 
            (b := baseCoins0) 
            (r := oldRC) 
            (s := oldSC) as [H7 [H8 H9]]. nra.
            destruct fissionFee. simpl. nra.
            - destruct fissionFee. simpl. 
            destruct reactorstate_assumption with 
            (b := baseCoins0) 
            (r := oldRC) 
            (s := oldSC) as [H7 _].
            destruct reactorstate_assumption with 
            (b := oldBC) 
            (r := oldRC) 
            (s := oldSC) as [H8 _].
            apply Rplus_pos_pos. lra.
            unfold Rdiv. apply Rmult_pos_pos. nra. apply Rinv_pos. apply H8.
        }
        assert (((oldSC +
        baseCoins0 * (1 - extract_value fissionFee) *
        oldSC / oldBC) * oldER /
        (oldBC + baseCoins0)) = (oldSC * oldER) / (oldBC * alpha)) as H8.
        {
            unfold alpha. field_simplify. reflexivity. split.
            - pose proof basecoin_assumption (oldBC) as H8. nra.
            - split.
                * pose proof basecoin_assumption (oldBC) as H8.
                pose proof basecoin_assumption (baseCoins0) as H9.
                destruct fissionFee. simpl. nra.
                * pose proof basecoin_assumption (oldBC) as H8.
                pose proof basecoin_assumption (baseCoins0) as H9. nra.
            - split.
                * pose proof basecoin_assumption (oldBC) as H8. nra.
                * pose proof basecoin_assumption (oldBC) as H8.
                pose proof basecoin_assumption (baseCoins0) as H9. nra.            
        }
        unfold Rmin in f. destruct Rle_dec in f.
        + unfold Rmin in f'. destruct Rle_dec in f'.
            * unfold f. unfold f'. 
            rewrite Rmult_div_swap with 
            (r1 := (1 - extract_value qStar) * oldBC)
            (r2 := alpha)
            (r3 := oldRC). 
            apply Rmult_gt_compat_l with 
            (r := (1 - extract_value qStar) * oldBC / oldRC) in H7. nra.
            destruct qStar. simpl. 
            pose proof basecoin_assumption (oldBC) as H9.
            pose proof reservecoin_assumption (oldRC) as H10.
            unfold Rdiv. apply Rmult_pos_pos.
            nra. apply Rinv_pos. apply H10.
            * unfold f. unfold f'. rewrite H8. apply Rnot_le_gt in n.
            rewrite H8 in n. pose proof n as ncopy. 
            apply Ropp_gt_lt_contravar in n.
            apply Rplus_lt_compat_r with (r := 1) in n.
            destruct qStar. simpl. simpl in n.
            rewrite Rplus_comm with (r1 := -x) in n.
            rewrite Rplus_comm with (r2 := 1) in n.
            rewrite <- Rminus_def in n. rewrite <- Rminus_def in n.
            apply Rmult_lt_compat_r with (r := oldBC) in n.
            apply a_gt_b_imp_a_mult_c_gt_b with (c := alpha) in n.
            apply Rmult_lt_compat_r with (r := /oldRC) in n.
            rewrite <- Rdiv_def in n. rewrite <- Rdiv_def in n.
            apply Rgt_ge. apply n.
            pose proof reservecoin_assumption (oldRC) as H9. 
            pose proof basecoin_assumption (oldBC) as H10.
            pose proof stablecoin_assumption (oldSC) as H11.
            apply Rinv_pos. apply H9.
            simpl in r. simpl in f. simpl in H6. simpl in ncopy.
            apply Rmult_pos_pos. apply Rgt_minus. apply Rgt_trans with (r2 := x).
            destruct a. lra. apply ncopy. 
            pose proof basecoin_assumption (oldBC) as H9. apply H9.
            apply H7. pose proof basecoin_assumption (oldBC) as H9. apply H9.
        + unfold Rmin in f'.
        assert (oldSC * oldER / (oldBC * alpha) < oldSC * oldER / oldBC) as H9.
        {
            apply a_div_b_mult_c_lt_a_div_b with (a := oldSC * oldER) (b := oldBC) (c := alpha).
            - pose proof stablecoin_assumption (oldSC) as H9.
            pose proof exchangerate_assumption (oldER) as H10.
            apply Rmult_pos_pos. nra. nra.
            - pose proof basecoin_assumption (oldBC) as H9. apply H9.
            - apply H7.
        }
        destruct Rle_dec in f'.
            * apply Rnot_le_gt in n. rewrite H8 in r.
            assert (extract_value qStar < oldSC * oldER / oldBC) as H10.
            {
                apply Rle_lt_trans with (r2 := oldSC * oldER / (oldBC * alpha)).
                - apply r.
                - apply H9.
            }
            nra. 
            * unfold f. unfold f'. rewrite H8. apply Rnot_le_gt in n.
            apply Rnot_le_gt in n0. rewrite H8 in n0. pose proof H9 as H9copy.
            apply Ropp_lt_gt_contravar in H9.
            apply Rplus_lt_compat_r with (r := 1) in H9.
            rewrite Rplus_comm with (r2 := 1) in H9.
            rewrite Rplus_comm with (r2 := 1) in H9.
            rewrite <- Rminus_def in H9. rewrite <- Rminus_def in H9.
            apply Rmult_lt_compat_r with (r := oldBC) in H9.
            apply a_gt_b_imp_a_mult_c_gt_b with (c := alpha) in H9.
            apply Rmult_lt_compat_r with (r := /oldRC) in H9.
            rewrite <- Rdiv_def in H9. rewrite <- Rdiv_def in H9.
            apply Rgt_ge. apply H9.
            pose proof reservecoin_assumption (oldRC) as H10.
            apply Rinv_pos. apply H10.
            apply Rmult_pos_pos. apply Rgt_minus. destruct qStar. simpl in n.
            simpl in n0. apply Rgt_trans with (r2 := x).
            destruct a. lra. apply n0. 
            pose proof basecoin_assumption (oldBC) as H10. apply H10.
            apply H7. pose proof basecoin_assumption (oldBC) as H10. apply H10.
        (*Fusion Case*)
        - unfold execute in H3. unfold fusion_reaction in H3.
        simpl in H3. rewrite H3. 
        destruct s1 as [[[oldBC oldSC oldRC] oldER] oldT].
        destruct s2 as [[[newBC newSC newRC] newER] newT].
        unfold fusion_ratio. unfold get_stablecoins. unfold get_basecoins. unfold get_reservecoins.
        simpl.
        unfold fusion_output in H3. unfold stablecoin_price in H3. 
        unfold reservecoin_price in H3. unfold get_basecoins in H3. 
        unfold get_reservecoins in H3. unfold get_stablecoins in H3. 
        unfold fusion_ratio in H3. simpl in H3. simpl. 
        set (f' := Rmin (extract_value qStar)
        ((oldSC - baseCoins0 * oldSC / oldBC) * oldER / (oldBC - baseCoins0 * (1 - extract_value fusionFee)))).
        set (f :=  Rmin (extract_value qStar) (oldSC * oldER / oldBC)).
        assert 
        (
            (1 - f') * (oldBC - baseCoins0 * (1 - extract_value fusionFee)) / (oldRC - baseCoins0 * oldRC / oldBC) = 
            ((1 - f') * oldBC * ((1 - (((1 - extract_value fusionFee) * baseCoins0) / (oldBC))) / (1 - (baseCoins0 / oldBC)))) / (oldRC)
        ) as H6.
        { 
            rewrite Rmult_div_swap with 
            (r1 := (1 - f') * oldBC) 
            (r2 := ((1 - (1 - extract_value fusionFee) * baseCoins0 / oldBC) / (1 - baseCoins0 / oldBC)))
            (r3 := oldRC).
            rewrite a_div_b_mult_c_div_d_imp_a_mult_c_div_b_mult_d with
            (a := (1 - f') * oldBC)
            (b := oldRC)
            (d := (1 - baseCoins0 / oldBC)).
            rewrite Rmult_assoc with
            (r1 := 1 - f')
            (r2 := oldBC)
            (r3 := (1 - (1 - extract_value fusionFee) * baseCoins0 / oldBC)).
            rewrite Rmult_minus_distr_l with
            (r1 := oldBC)
            (r2 := 1)
            (r3 := (1 - extract_value fusionFee) * baseCoins0 / oldBC).
            rewrite Rmult_1_r.
            rewrite a_mult_b_div_a_eq_b with
            (a := oldBC)
            (b := (1 - extract_value fusionFee) * baseCoins0).
            rewrite Rmult_minus_distr_l with
            (r1 := oldRC)
            (r2 := 1)
            (r3 := baseCoins0 / oldBC).
            rewrite Rmult_1_r.
            rewrite Rmult_div_assoc with
            (r1 := oldRC)
            (r2 := baseCoins0)
            (r3 := oldBC).
            rewrite Rmult_comm with
            (r1 := (1 - extract_value fusionFee))
            (r2 := baseCoins0).
            rewrite Rmult_comm with
            (r1 := oldRC)
            (r2 := baseCoins0).
            reflexivity.
            pose proof basecoin_assumption (oldBC) as H6.
            nra.    
        }
        destruct Rlt_dec as [H7 | H8]. simpl.
        * fold f'. rewrite H6.
        set (alpha := ((1 - (1 - extract_value fusionFee) * baseCoins0 / oldBC) / (1 - baseCoins0 / oldBC))).
        assert (alpha > 1) as H8.
        {
            unfold alpha. apply division_greater_than_one.
            - rewrite Rminus_def. 
            rewrite Rminus_def with (r1 := 1) (r2 := baseCoins0 / oldBC).
            apply Rplus_gt_compat_l with (r := 1). apply Ropp_lt_gt_contravar. 
            unfold Rdiv. apply Rmult_gt_compat_r with (r := / oldBC).
            apply Rinv_pos. pose proof basecoin_assumption (oldBC) as H9. apply H9.
            rewrite <- Rmult_1_l with (r := baseCoins0) at 1.
            apply Rmult_gt_compat_r with (r := baseCoins0).
            pose proof basecoin_assumption (baseCoins0) as H9. apply H9.
            destruct fusionFee. simpl. nra.
            - apply Rgt_minus. unfold Rdiv. rewrite Rmult_comm. 
            rewrite Rinv_r_sym with (r := /oldBC). rewrite Rinv_inv.
            apply Rmult_gt_compat_l with
            (r := /oldBC)
            (r1 := oldBC)
            (r2 := baseCoins0). apply Rinv_pos. pose proof basecoin_assumption (oldBC) as H9.
            apply H9. apply H7. apply Rinv_neq_0_compat. pose proof basecoin_assumption (oldBC) as H9. nra.    
        }
        assert (((oldSC - ((baseCoins0 * oldSC) / oldBC)) * oldER / (oldBC - baseCoins0 * (1 - extract_value fusionFee))) = (oldSC * oldER) / (oldBC * alpha)) as H9.
        {
            unfold alpha. field_simplify. reflexivity. split.
            - pose proof basecoin_assumption (oldBC) as H9. nra.
            - split.
                * nra.
                * destruct fusionFee. simpl. apply Rminus_eq_contra.
                apply a_lt_b_imp_a_mult_c_lt_b with (c := 1 - x) in H7 as H9.
                rewrite Rmult_comm in H9. nra. pose proof basecoin_assumption (baseCoins0) as H9. nra.
                apply Rplus_lt_reg_l with (r := -1). field_simplify. apply Ropp_pos. nra.
            - split.
                * pose proof basecoin_assumption (oldBC) as H9. nra.
                * destruct fusionFee. simpl. apply Rminus_eq_contra.
                apply a_lt_b_imp_a_mult_c_lt_b with (c := 1 - x) in H7 as H9.
                rewrite Rmult_comm in H9. nra. pose proof basecoin_assumption (baseCoins0) as H9. nra.
                apply Rplus_lt_reg_l with (r := -1). field_simplify. apply Ropp_pos. nra.            
        }
        unfold Rmin in f. destruct Rle_dec in f.
        + unfold Rmin in f'. destruct Rle_dec in f'.
            (* f = q*, f' = q* *)
            unfold f. unfold f'. 
            rewrite Rmult_div_swap with 
            (r1 := (1 - extract_value qStar) * oldBC)
            (r2 := alpha)
            (r3 := oldRC). 
            apply Rmult_gt_compat_l with 
            (r := (1 - extract_value qStar) * oldBC / oldRC) in H8. nra.
            destruct qStar. simpl. 
            pose proof basecoin_assumption (oldBC) as H10.
            pose proof reservecoin_assumption (oldRC) as H11.
            unfold Rdiv. apply Rmult_pos_pos.
            nra. apply Rinv_pos. apply H11.
            (* f = q*, f' = ratio *)
            unfold f. unfold f'. rewrite H9. apply Rnot_le_gt in n.
            rewrite H9 in n. pose proof n as ncopy. 
            apply Ropp_gt_lt_contravar in n.
            apply Rplus_lt_compat_r with (r := 1) in n.
            destruct qStar. simpl. simpl in n.
            rewrite Rplus_comm with (r1 := -x) in n.
            rewrite Rplus_comm with (r2 := 1) in n.
            rewrite <- Rminus_def in n. rewrite <- Rminus_def in n.
            apply Rmult_lt_compat_r with (r := oldBC) in n.
            apply a_gt_b_imp_a_mult_c_gt_b with (c := alpha) in n.
            apply Rmult_lt_compat_r with (r := /oldRC) in n.
            rewrite <- Rdiv_def in n. rewrite <- Rdiv_def in n.
            apply Rgt_ge. apply n.
            pose proof reservecoin_assumption (oldRC) as H10. 
            pose proof basecoin_assumption (oldBC) as H11.
            pose proof stablecoin_assumption (oldSC) as H12.
            apply Rinv_pos. apply H10.
            simpl in r. simpl in f. simpl in H6. simpl in ncopy.
            apply Rmult_pos_pos. apply Rgt_minus. apply Rgt_trans with (r2 := x).
            destruct a. lra. apply ncopy. 
            pose proof basecoin_assumption (oldBC) as H10. apply H10.
            apply H8. pose proof basecoin_assumption (oldBC) as H10. apply H10.
        + unfold Rmin in f'.
            assert (oldSC * oldER / (oldBC * alpha) < oldSC * oldER / oldBC) as H10.
            {
                apply a_div_b_mult_c_lt_a_div_b with (a := oldSC * oldER) (b := oldBC) (c := alpha).
                - pose proof stablecoin_assumption (oldSC) as H10.
                pose proof exchangerate_assumption (oldER) as H11.
                apply Rmult_pos_pos. nra. nra.
                - pose proof basecoin_assumption (oldBC) as H10. apply H10.
                - apply H8.
            }
            destruct Rle_dec in f'.
            (* f = ratio, f' = q* This case is not possible. Arriving at a contradiction *)
            apply Rnot_le_gt in n. rewrite H9 in r.
            assert (extract_value qStar < oldSC * oldER / oldBC) as H11.
            {
                apply Rle_lt_trans with (r2 := oldSC * oldER / (oldBC * alpha)).
                - apply r.
                - apply H10.
            }
            nra. 
            (* f = ratio, f' = ratio *)
            unfold f. unfold f'. rewrite H9. apply Rnot_le_gt in n.
            apply Rnot_le_gt in n0. rewrite H9 in n0. pose proof H10 as H10copy.
            apply Ropp_lt_gt_contravar in H10.
            apply Rplus_lt_compat_r with (r := 1) in H10.
            rewrite Rplus_comm with (r2 := 1) in H10.
            rewrite Rplus_comm with (r2 := 1) in H10.
            rewrite <- Rminus_def in H10. rewrite <- Rminus_def in H10.
            apply Rmult_lt_compat_r with (r := oldBC) in H10.
            apply a_gt_b_imp_a_mult_c_gt_b with (c := alpha) in H10.
            apply Rmult_lt_compat_r with (r := /oldRC) in H10.
            rewrite <- Rdiv_def in H10. rewrite <- Rdiv_def in H10.
            apply Rgt_ge. apply H10.
            pose proof reservecoin_assumption (oldRC) as H11.
            apply Rinv_pos. apply H11.
            apply Rmult_pos_pos. apply Rgt_minus. destruct qStar. simpl in n.
            simpl in n0. apply Rgt_trans with (r2 := x).
            destruct a. lra. apply n0. 
            pose proof basecoin_assumption (oldBC) as H11. apply H11.
            apply H8. pose proof basecoin_assumption (oldBC) as H11. apply H11.
        * simpl. unfold f. nra.
        (* Beta Decay Positive *)
        - (* Unfolding and simplifying *)
        set (f := fusion_ratio (stableCoinState s1)).
        set (f' := fusion_ratio (stableCoinState s2)).
        destruct s1 as [[[oldBC oldSC oldRC] oldER] oldT] eqn:S1.
        destruct s2 as [[[newBC newSC newRC] newER] newT] eqn:S2.
        unfold execute in H3. unfold beta_decay_pos_reaction in H3.
        unfold stablecoin_price in H3. unfold reservecoin_price in H3. 
        unfold get_basecoins in H3. unfold get_reservecoins in H3. unfold fusion_ratio in H3.
        unfold get_stablecoins in H3. rewrite beta_decay_pos_output_alt in H3. simpl in H3.
        set (
            decay_fee := 
            beta_decay_pos_fee
            (BetaDecayPosEvent
                reserveCoins0) oldT
            {|
            reactorState :=
                {|
                baseCoins := oldBC;
                stableCoins := oldSC;
                reserveCoins := oldRC
                |};
            exchangeRate := oldER
            |} t
        ) in H3.
        unfold stablecoin_price in H3. unfold reservecoin_price in H3.
        simpl in H3. rewrite H3.
        destruct Rlt_dec as [H6 | H7].
        + simpl.
        (* Creating alpha term *)
        assert (oldRC - reserveCoins0 = oldRC * (1 - (reserveCoins0 / oldRC))) as H7.
        {
            field_simplify.
            - reflexivity.
            - pose proof reservecoin_assumption (oldRC) as H7. nra.
        }
        rewrite H7.
        (* Writing new price of reserve coin using alpha *)
        assert ((1 - f') * oldBC / (oldRC * (1 - reserveCoins0 / oldRC)) = (((1 - f') * oldBC) * (1 / (1 - reserveCoins0 / oldRC))) / oldRC) as H8.
        {
            field_simplify; try (reflexivity); split; repeat nra.
        }
        rewrite H8.
        set (alpha := 1 / (1 - reserveCoins0 / oldRC)).
        assert (alpha > 1) as H9.
        {
            apply division_greater_than_one.
            - field_simplify.
                + apply division_less_than_one.
                    * rewrite Rplus_comm. apply Rplus_neg_lt.
                    pose proof reservecoin_assumption (reserveCoins0) as H9. 
                    nra.
                    * pose proof reservecoin_assumption (oldRC) as H9. nra.
                + pose proof reservecoin_assumption (oldRC) as H9. nra.
            - apply Rgt_minus. apply division_less_than_one.
                + nra.
                + pose proof reservecoin_assumption (oldRC) as H9. nra.
        }
        set (alpha' := 1 + ((reserveCoins0 * (1 - decay_fee) * (1 - f)) / (f * oldRC))).
        (* Rewriting f' using alpha'*)
        assert (
            (oldSC + reserveCoins0 * (1 - decay_fee) * (1 - f) * oldSC / (f * oldRC)) * oldER / oldBC = 
            (oldSC * alpha' * oldER) / oldBC
        ) as H10.
        {
            (* TODO: Ask how this proof works. Much simpler *)
            (* unfold alpha'; field_simplify_eq; try reflexivity; repeat split; 
            apply Rgt_not_eq; try apply reservecoin_assumption; try apply basecoin_assumption. *)

            unfold alpha'. field_simplify.
            - reflexivity.
            - split.
                + nra.
                + split.
                    * apply Rgt_not_eq. unfold f. rewrite <- S1. apply fusion_ratio_gt_0.
                    * apply Rgt_not_eq; apply basecoin_assumption. 
            - split.
                + nra.
                + split.
                    * apply Rgt_not_eq. unfold f. rewrite <- S1. apply fusion_ratio_gt_0.
                    * apply Rgt_not_eq; apply basecoin_assumption.
        }
        (* alpha' > 1 *)
        assert (alpha' > 1) as H11.
        {
            unfold alpha'; apply Rplus_pos_gt; unfold Rdiv; apply Rmult_pos_pos.
            - apply Rmult_pos_pos.
                + apply Rmult_pos_pos.
                    * apply reservecoin_assumption.
                    * apply Rgt_minus; unfold decay_fee; apply Rgt_lt.
                    assert (oldT = s1.(reactions)) as H13 by (rewrite S1; auto).
                    assert (
                        {|
                            reactorState :=
                            {|
                                baseCoins := oldBC;
                                stableCoins := oldSC;
                                reserveCoins := oldRC
                            |};
                            exchangeRate := oldER
                        |} = s1.(stableCoinState)
                    ) as H14 by (rewrite S1; auto).
                    rewrite H13; rewrite H14. 
                    apply beta_decay_pos_fee_lt_1.
                (* 1 - f > 0 *)
                + apply Rgt_minus. unfold f. rewrite <- S1. apply fusion_ratio_lt_1.
            (* / (f * oldRC) > 0 *)
            - apply Rinv_pos; apply Rmult_pos_pos.
                + unfold f. rewrite <- S1. apply fusion_ratio_gt_0.
                + apply reservecoin_assumption.
        }
        injection H3. intros. unfold f, f'. unfold fusion_ratio. simpl. unfold Rmin. destruct Rle_dec. 
        * destruct Rle_dec.
            {
                (* f = q*, f' = q* *)
                unfold f; unfold f'. 
                rewrite Rmult_div_swap with 
                (r1 := (1 - extract_value qStar) * oldBC)
                (r2 := alpha)
                (r3 := oldRC).
                apply Rmult_gt_compat_l with 
                (r := (1 - extract_value qStar) * oldBC / oldRC) in H9.
                - nra.
                - destruct qStar; simpl; unfold Rdiv; repeat (apply Rmult_pos_pos);
                try (nra);
                try (apply Rinv_pos; apply reservecoin_assumption);
                try (apply basecoin_assumption).        
            }
            {
                (* f = ratio, f' q* *)
                apply Rmult_ge_compat_r.
                - apply Rgt_ge; apply Rinv_pos; apply reservecoin_assumption.
                - rewrite Rmult_assoc; rewrite Rmult_comm with (r1 := oldBC) (r2 := alpha); rewrite <- Rmult_assoc. apply Rmult_ge_compat_r.
                    + apply Rgt_ge; apply basecoin_assumption.
                    + unfold f, f'; simpl in f, f'; fold f in H13; rewrite H0, H13, H14 in r; 
                    apply Rge_trans with (r2 := (1 - ((oldER * oldSC * alpha') / oldBC)) * alpha).
                        * apply Rmult_ge_compat_r.
                            { nra. }
                            { 
                                unfold Rminus; apply Rplus_ge_compat_l;
                                apply Ropp_le_ge_contravar;
                                rewrite H10 in r; nra.   
                            }
                        * assert ((1 - oldER * oldSC * alpha' / oldBC) * alpha = (1 - oldSC * oldER / oldBC) * ((1 - ((reserveCoins0 * (1 - decay_fee)) / (oldRC))) / (1 - (reserveCoins0 / oldRC)))) as H15.
                        {
                            unfold alpha, alpha'; unfold f; unfold fusion_ratio; unfold Rmin; simpl; destruct Rle_dec.
                            - nra.
                            - field_simplify.
                                + reflexivity.
                                + repeat split.
                                    * apply Rgt_not_eq; apply reservecoin_assumption.
                                    * apply Rgt_not_eq; apply Rgt_minus; nra.
                                    * apply Rgt_not_eq; apply basecoin_assumption.
                                + repeat split.
                                    * apply Rgt_not_eq; apply reservecoin_assumption.
                                    * apply Rgt_not_eq; apply Rgt_minus; nra.
                                    * apply Rgt_not_eq; apply basecoin_assumption.
                                    * apply Rgt_not_eq; apply exchangerate_assumption.
                                    * apply Rgt_not_eq; apply stablecoin_assumption.
                        }
                        rewrite H15; rewrite <- Rmult_1_r; apply Rmult_ge_compat_l.
                            {
                                apply Rnot_le_gt in n; destruct qStar in n; 
                                simpl in n; nra.
                            }
                            {
                                apply Rgt_ge; apply division_greater_than_one.
                                - unfold Rdiv; apply Rminus_gt; unfold Rminus; field_simplify.
                                    + unfold Rdiv; repeat apply Rmult_pos_pos.
                                        * apply reservecoin_assumption.
                                        * unfold decay_fee. 
                                        assert (oldT = s1.(reactions)) as H16.
                                        { rewrite S1. auto. }
                                        assert (
                                            {|
                                                reactorState :=
                                                {|
                                                    baseCoins := oldBC;
                                                    stableCoins := oldSC;
                                                    reserveCoins := oldRC
                                                |};
                                                exchangeRate := oldER
                                            |} = s1.(stableCoinState)
                                        ) as H17.
                                        { rewrite S1. auto. }
                                        rewrite H16, H17; apply beta_decay_pos_fee_gt_0.
                                        * apply Rinv_pos; apply reservecoin_assumption.
                                    + apply Rgt_not_eq; apply reservecoin_assumption.
                                - apply Rgt_minus; apply division_less_than_one.
                                    + nra.
                                    + apply reservecoin_assumption.   
                            }
            }
        * destruct Rle_dec.
            {
                (* f = q*, f' = ratio *)
                apply Rnot_le_gt in n.
                -
                (*
                 * Proving that f' != newSC * newER / newBC to arrive at a 
                 * contradiction
                 *)
                assert (extract_value qStar <= oldSC * alpha' * oldER / oldBC) as H15.
                {
                    apply Rle_trans with (r2 := oldSC * oldER / oldBC).
                    - nra.
                    - unfold Rdiv; apply Rmult_le_compat_r.
                        + apply Rlt_le; apply Rinv_pos; apply basecoin_assumption.
                        + apply Rmult_le_compat_r.
                            * apply Rlt_le; apply exchangerate_assumption. 
                            * apply Rlt_le; apply a_ge_b_imp_a_mult_c_gt_b.
                                { apply stablecoin_assumption. }
                                { nra. }
                                { nra. }
                }
                simpl in f, f'. fold f in H13. 
                assert (oldSC * alpha' = newSC) as H16.
                {
                    unfold alpha'. rewrite H13. rewrite Rmult_plus_distr_l. nra.
                }
                rewrite <- H0 in H15. rewrite H16 in H15. rewrite <- H14 in H15.
                nra.
            }
            {
                (* f = ratio, f' = ratio *)
                apply Rmult_ge_compat_r.
                - apply Rgt_ge; apply Rinv_pos; apply reservecoin_assumption.
                - rewrite Rmult_assoc; rewrite Rmult_comm with (r1 := oldBC) (r2 := alpha); rewrite <- Rmult_assoc. apply Rmult_ge_compat_r.
                    + apply Rgt_ge; apply basecoin_assumption.
                    + unfold f, f'. simpl in f, f'. fold f in H13. rewrite H0, H13, H14.
                    rewrite H10. assert ((1 - oldSC * alpha' * oldER / oldBC) * alpha = (1 - oldSC * oldER / oldBC) * ((1 - ((reserveCoins0 * (1 - decay_fee)) / (oldRC))) / (1 - (reserveCoins0 / oldRC)))) as H15.
                    {
                        unfold alpha, alpha'; unfold f; unfold fusion_ratio; unfold Rmin; simpl; destruct Rle_dec.
                        - nra.
                        - field_simplify.
                            + reflexivity.
                            + repeat split.
                                * apply Rgt_not_eq; apply reservecoin_assumption.
                                * apply Rgt_not_eq; apply Rgt_minus; nra.
                                * apply Rgt_not_eq; apply basecoin_assumption.
                            + repeat split.
                                * apply Rgt_not_eq; apply reservecoin_assumption.
                                * apply Rgt_not_eq; apply Rgt_minus; nra.
                                * apply Rgt_not_eq; apply basecoin_assumption.
                                * apply Rgt_not_eq; apply exchangerate_assumption.
                                * apply Rgt_not_eq; apply stablecoin_assumption.
                    } 
                    rewrite H15; rewrite <- Rmult_1_r; apply Rmult_ge_compat_l.
                        {
                            apply Rnot_le_gt in n0. destruct qStar in n0. 
                            simpl in n0. nra.
                        }
                        {
                            apply Rgt_ge; apply division_greater_than_one.
                            - unfold Rdiv; apply Rminus_gt; unfold Rminus; field_simplify.
                                + unfold Rdiv; repeat apply Rmult_pos_pos.
                                    * apply reservecoin_assumption.
                                    * unfold decay_fee. 
                                    assert (oldT = s1.(reactions)) as H16.
                                    { rewrite S1. auto. }
                                    assert (
                                        {|
                                            reactorState :=
                                            {|
                                                baseCoins := oldBC;
                                                stableCoins := oldSC;
                                                reserveCoins := oldRC
                                            |};
                                            exchangeRate := oldER
                                        |} = s1.(stableCoinState)
                                    ) as H17.
                                    { rewrite S1. auto. }
                                    rewrite H16, H17; apply beta_decay_pos_fee_gt_0.
                                    * apply Rinv_pos; apply reservecoin_assumption.
                                + apply Rgt_not_eq; apply reservecoin_assumption.
                            - apply Rgt_minus; apply division_less_than_one.
                                + nra.
                                + apply reservecoin_assumption.   
                        }
            }
        + assert (s1 = s2) as H6.
        { rewrite S1, S2, H3; reflexivity. }
        unfold f', f, fusion_ratio; rewrite H3; nra.

    (* Beta Decay Negative Event *) 
    - (* Unfolding and simplifying *)
        set (f := fusion_ratio (stableCoinState s1)).
        set (f' := fusion_ratio (stableCoinState s2)).
        destruct s1 as [[[oldBC oldSC oldRC] oldER] oldT] eqn:S1.
        destruct s2 as [[[newBC newSC newRC] newER] newT] eqn:S2.
        unfold execute in H3. unfold beta_decay_neg_reaction in H3.
        unfold stablecoin_price in H3. unfold reservecoin_price in H3. 
        unfold get_basecoins in H3. unfold get_reservecoins in H3. unfold fusion_ratio in H3.
        unfold get_stablecoins in H3. rewrite beta_decay_neg_output_alt in H3. simpl in H3.
        set (
            decay_fee := 
            beta_decay_neg_fee
            (BetaDecayNegEvent
                stableCoins0) oldT
            {|
            reactorState :=
                {|
                baseCoins := oldBC;
                stableCoins := oldSC;
                reserveCoins := oldRC
                |};
            exchangeRate := oldER
            |} t
        ) in H3.
        unfold stablecoin_price in H3. unfold reservecoin_price in H3.
        simpl in H3. rewrite H3.
        destruct Rlt_dec as [H6 | H7].
        + simpl in f, f'. simpl. fold f.
        (* Creating alpha term *)
        assert (
            oldRC + stableCoins0 * (1 - decay_fee) * f * oldRC / ((1 - f) * oldSC) =
            oldRC * (1 + stableCoins0 * (1 - decay_fee) * f / ((1 - f) * oldSC))
        ) as H7.
        {
            field_simplify.
            - reflexivity.
            - repeat split.
                + apply Rgt_not_eq. apply stablecoin_assumption.
                + apply Rgt_not_eq. apply Rgt_minus. apply fusion_ratio_lt_1.
            - repeat split.
                + apply Rgt_not_eq. apply stablecoin_assumption.
                + apply Rgt_not_eq. apply Rgt_minus. apply fusion_ratio_lt_1.
        }
        set (alpha := (1 + stableCoins0 * (1 - decay_fee) * f / ((1 - f) * oldSC))).  
        rewrite H7. fold alpha.
        set (alpha' := (1 - (stableCoins0 / oldSC)) / alpha).
        assert (oldSC - stableCoins0 = oldSC * (1 - stableCoins0 / oldSC)) as H8.
        { 
            field_simplify. 
            - reflexivity.
            - apply Rgt_not_eq. apply stablecoin_assumption. 
        }
        assert (0 < f < 1) as F_RANGE.
        {
            split; unfold f; try (apply fusion_ratio_gt_0); try (apply fusion_ratio_lt_1).
        }
        assert (0 < f' < 1) as F'_RANGE.
        {
            split; unfold f'; try (apply fusion_ratio_gt_0); try (apply fusion_ratio_lt_1).
        }
        injection H3. intros. unfold f, f'. unfold fusion_ratio. simpl. unfold Rmin. destruct Rle_dec. 
        * destruct Rle_dec.
            {
                (* f = q*, f' = q* *)
                - unfold is_depeg in H5. unfold fusion_ratio, Rmin in H5.
                destruct Rle_dec in H5.
                    + assert (extract_value qStar = extract_value qStar) as H12.
                    { reflexivity. } 
                    apply H5 with (x := stableCoins0) in H12. contradiction.
                    + contradiction.
            }
            {
                (* f = ratio, f' = q* *)
                (*
                 * Proving that f' != q* to arrive at a 
                 * contradiction
                 *)
                assert (extract_value qStar > newSC * newER / newBC) as H12.
                {
                    apply Rgt_trans with (r2 := oldSC * oldER / oldBC).
                    - nra.
                    - rewrite H0, H11. unfold Rdiv. apply Rmult_gt_compat_r.
                        + apply Rinv_pos; apply basecoin_assumption.
                        + apply Rmult_gt_compat_r.
                            * apply exchangerate_assumption. 
                            * rewrite H10. rewrite H8. rewrite <- Rmult_1_r at 1.
                            apply Rmult_gt_compat_l.
                                -- apply stablecoin_assumption.
                                -- apply Rgt_minus_pos. apply Rdiv_pos_pos.
                                    ++ apply stablecoin_assumption.
                                    ++ apply stablecoin_assumption.
                } nra.
            }
        * destruct Rle_dec.
            {
                (* f = q*, f' = ratio *)
                - unfold is_depeg in H5. unfold fusion_ratio, Rmin in H5.
                destruct Rle_dec in H5.
                    + assert (extract_value qStar = extract_value qStar) as H12.
                    { reflexivity. } 
                    apply H5 with (x := stableCoins0) in H12. contradiction.
                    + contradiction.
            }
            {
                (* f = ratio, f' = ratio *)
                rewrite H0, H10, H11, H8.
                set (q := oldSC * oldER / oldBC).
                assert (
                    (1 - oldSC * (1 - stableCoins0 / oldSC) * oldER / oldBC) * oldBC / (oldRC * alpha) =
                    ((1 - oldSC * (1 - stableCoins0 / oldSC) * oldER / oldBC) * oldBC / (oldRC * alpha)) * ((1 - q) / (1 - q))
                ) as H12.
                {
                    assert ((1 - q) / (1 - q) = 1).
                    { 
                        apply Rdiv_diag. apply Rgt_not_eq. apply Rgt_minus.
                        unfold f, fusion_ratio, Rmin in F_RANGE. simpl in F_RANGE.
                        destruct Rle_dec in F_RANGE.
                        - contradiction.
                        - destruct F_RANGE. unfold q. nra.
                    }
                    rewrite H12. rewrite Rmult_1_r. reflexivity.
                }
                rewrite H12.
                rewrite a_div_b_mult_c_div_d_imp_a_mult_c_div_b_mult_d.
                assert (
                    oldSC * (1 - stableCoins0 / oldSC) * oldER / oldBC = q * (1 - stableCoins0 / oldSC)
                ) as H13.
                {
                    unfold q. field_simplify_eq.
                    - reflexivity.
                    - split; apply Rgt_not_eq; try (apply basecoin_assumption); try (apply stablecoin_assumption).
                }
                rewrite H13. rewrite Rmult_comm. rewrite Rmult_comm with (r1 := (1 - q * (1 - stableCoins0 / oldSC))).
                rewrite <- Rmult_assoc. rewrite Rmult_assoc with (r1 := oldRC).
                rewrite <- a_div_b_mult_c_div_d_imp_a_mult_c_div_b_mult_d.
                apply Rgt_ge. rewrite <- Rmult_1_r. apply Rmult_gt_compat_l.
                - unfold Rdiv. repeat apply Rmult_pos_pos.
                    + apply Rgt_minus. unfold f, fusion_ratio, Rmin in F_RANGE. simpl in F_RANGE.
                    destruct Rle_dec in F_RANGE.
                        * contradiction.
                        * destruct F_RANGE. unfold q. nra.
                    + apply basecoin_assumption.
                    + apply Rinv_pos. apply reservecoin_assumption.
                - unfold alpha, f, fusion_ratio, Rmin. destruct Rle_dec.
                    + contradiction.
                    + simpl. fold q. rewrite Rmult_comm with (r1 := 1 + stableCoins0 * (1 - decay_fee) * q / ((1 - q) * oldSC)).
                    rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
                    assert (
                        (1 - q + (1 - q) * (stableCoins0 * (1 - decay_fee) * q / ((1 - q) * oldSC))) =
                        (1 - q * (1 - ((stableCoins0 * (1 - decay_fee)) / (oldSC))))
                    ) as H14.
                    {
                        field_simplify.
                        - reflexivity.
                        - apply Rgt_not_eq. apply stablecoin_assumption.
                        - repeat split.
                            + apply Rgt_not_eq. apply stablecoin_assumption.
                            + apply Rgt_not_eq. apply Rgt_minus. unfold f, fusion_ratio, Rmin in F_RANGE. simpl in F_RANGE.
                            destruct Rle_dec in F_RANGE.
                                * contradiction.
                                * destruct F_RANGE. unfold q. nra. 
                    }
                    rewrite H14. apply division_greater_than_one.
                        * unfold Rminus. apply Rplus_gt_compat_l.
                        apply Ropp_lt_gt_contravar. apply Rmult_lt_compat_l.
                            -- unfold q. unfold f, fusion_ratio, Rmin in F_RANGE. simpl in F_RANGE.
                            destruct Rle_dec in F_RANGE.
                                ++ contradiction.
                                ++ destruct F_RANGE. unfold q. nra.
                            -- apply Rplus_gt_compat_l. apply Ropp_lt_gt_contravar.
                            unfold Rdiv. apply Rmult_lt_compat_r.
                                ++ apply Rinv_pos. apply stablecoin_assumption.
                                ++ rewrite <- Rmult_1_r. apply Rmult_lt_compat_l.
                                    ** apply stablecoin_assumption.
                                    ** apply Rplus_neg_lt. apply Ropp_pos.
                                    unfold decay_fee. 
                                    assert (oldT = s1.(reactions)) as H15 by (rewrite S1; auto).
                                    assert (
                                        {|
                                            reactorState :=
                                            {|
                                                baseCoins := oldBC;
                                                stableCoins := oldSC;
                                                reserveCoins := oldRC
                                            |};
                                            exchangeRate := oldER
                                        |} = s1.(stableCoinState)
                                    ) as H16.
                                    { rewrite S1. auto. } rewrite H15, H16.
                                    apply beta_decay_neg_fee_gt_0.   
                        * apply Rgt_minus. apply a_lt_b_imp_a_mult_c_lt_b.
                            -- unfold q. unfold f, fusion_ratio, Rmin in F_RANGE. simpl in F_RANGE.
                            destruct Rle_dec in F_RANGE.
                                ++ contradiction.
                                ++ destruct F_RANGE. nra.
                            -- unfold Rminus. apply Rplus_neg_lt. apply Ropp_pos.
                            unfold Rdiv. apply Rmult_pos_pos.
                                ++ apply Rmult_pos_pos.
                                    ** apply stablecoin_assumption.
                                    ** apply Rgt_minus. unfold decay_fee.
                                    assert (oldT = s1.(reactions)) as H15 by (rewrite S1; auto).
                                    assert (
                                        {|
                                            reactorState :=
                                            {|
                                                baseCoins := oldBC;
                                                stableCoins := oldSC;
                                                reserveCoins := oldRC
                                            |};
                                            exchangeRate := oldER
                                        |} = s1.(stableCoinState)
                                    ) as H16.
                                    { rewrite S1. auto. } rewrite H15, H16.
                                    apply beta_decay_neg_fee_lt_1.
                                ++ apply Rinv_pos. apply stablecoin_assumption.
                            -- unfold f, fusion_ratio, Rmin in F_RANGE. simpl in F_RANGE.
                            destruct Rle_dec in F_RANGE.
                                ++ contradiction.
                                ++ destruct F_RANGE. unfold q. nra.    
            }
        + simpl. unfold f, f', fusion_ratio, Rmin. destruct Rle_dec.
            * destruct Rle_dec.
                -- nra.
                -- simpl. simpl in n, r. inversion H3. rewrite H0, H6, H9 in r. nra.
            * destruct Rle_dec.
                -- simpl. simpl in n, r. inversion H3. rewrite H0, H6, H9 in n. nra.
                -- simpl. inversion H3. nra.
    Qed.
End Theorem5.



