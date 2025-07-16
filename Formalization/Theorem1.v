From StableCoinFormalization Require Export Datatypes.
From StableCoinFormalization Require Export HelperFunctions.
From StableCoinFormalization Require Export Functions.
From StableCoinFormalization Require Export FunctionProofs.
From StableCoinFormalization Require Export HelperLemmas.
Require Export Lra.
Local Open Scope R_scope.
Module Theorem1.
    Import Datatypes.
    Import HelperFunctions.
    Import Functions.
    Import Lra.
    Import FunctionProofs.
    Import HelperLemmas.

    (*
     * state_0: state when the seller makes the offer
     * state_1: state just before when any potential buyer performs the beta + 
                reaction after the fission reaction. We are assuming the state_1
                occurs later in time compared to state_0 and need to state this
                assumption accordingly. 
     * timestamp: timestamp when any potential buyer performs the beta + 
                  reaction after the fission reaction. timestamp > timestamp
                  of the most recent reaction according to state_1
     * offer: offer which the seller makes
     *)
    Theorem peg_maintenance_upper_bound :
    forall
        (timestamp : nat) 
        (m : R)
        (state_0 : State)
        (state_1 : State) 
        (offer : Offer)
        (betaDecayPosFeeVal : R)
		(gamma : R)  
        (k rr fissFee b0 effFee primaryMarketOffer secondaryMarketOffer e0 e1 : R),
    (k > 0) ->
    (m > 0) ->
    (state_1 = execute (state_0) (FissionEvent (m)) (timestamp)) ->
    (e0 = target_price (state_0.(stableCoinState))) ->
    (e1 = target_price (state_1.(stableCoinState))) ->
    (betaDecayPosFeeVal = k * extract_value (betaDecayFee0)) ->
    rr = reserve_ratio (state_0.(stableCoinState)) ->
    fissFee = extract_value (fissionFee) ->
    b0 = extract_value (betaDecayFee0) ->
    effFee = get_effective_fee (timestamp) (state_0) (state_1) (gamma) (betaDecayPosFeeVal) (BuyStableCoin) ->
    offer.(action) = SellStableCoin ->
    primaryMarketOffer = get_primary_market_offer (timestamp) (state_0) (state_1) (gamma) (betaDecayPosFeeVal) (BuyStableCoin) ->
    secondaryMarketOffer = offer.(value) ->
    (/extract_value (qStar)) < rr ->
    ((1 + effFee) * target_price (state_0.(stableCoinState))) < (offer.(value)) ->
    (effFee >= 0) ->
    stablecoin_price (state_0.(stableCoinState)) <> 0 -> 
    betaDecayPosFeeVal < 1 ->
    e0 = e1 ->
    get_rational_choice (BuyStableCoin) (primaryMarketOffer) (secondaryMarketOffer) = Primary /\
    effFee < ((rr) / ((1 - fissFee) * (1 + ((rr - 1) * (1 - (k * b0)))))) - 1.
    
    Proof.
        intros.
        split.
        (*
         * Proving that choosing the secondary market for buying stable coins
         * is an irrational choice
         *)
        - unfold get_rational_choice. destruct Rlt_dec.
            + assert (primaryMarketOffer < secondaryMarketOffer).
            {
                rewrite H10. rewrite H11. unfold get_primary_market_offer.
                apply Rle_lt_trans with (r2 := (1 + get_effective_fee timestamp state_0 state_1 gamma betaDecayPosFeeVal BuyStableCoin) * target_price (stableCoinState state_0)); [| nra].
                - apply Rmult_le_compat_l; [| apply actual_price_le_target_price_neutron].
                    + apply Rplus_le_le_0_compat; lra.
            } lra.
            + reflexivity.
        (*
         * Proving the bound on the effective fee
         *)
        - rewrite H8. unfold get_effective_fee. 
        unfold base_coins_for_n_stable_coins.
        set (rP := reservecoin_price (stableCoinState state_0)).
        set (rP' := reservecoin_price (stableCoinState state_1)).
        set (sP := stablecoin_price (stableCoinState state_0)).
        set (sP' := stablecoin_price (stableCoinState state_1)).
        set (fusRat := fusion_ratio (stableCoinState state_0)).
        set (fusRat' := fusion_ratio (stableCoinState state_1)).
        set (alpha := (get_basecoins (state_0.(stableCoinState).(reactorState)) + m) / (get_basecoins (state_0.(stableCoinState).(reactorState)) + ((1 - fissFee) * m))).
        set (rC := get_reservecoins (state_0.(stableCoinState).(reactorState))).
        set (bC := get_basecoins (state_0.(stableCoinState).(reactorState))).
        set (sC' := get_stablecoins (state_1.(stableCoinState).(reactorState))).
        set (bC' := get_basecoins (state_1.(stableCoinState).(reactorState))).
        set (sC := get_stablecoins (state_0.(stableCoinState).(reactorState))).
        set (rC' := get_reservecoins (state_1.(stableCoinState).(reactorState))).
		assert (bC > 0) as HbC by (apply basecoin_assumption).
		assert (sC > 0) as HsC by (apply stablecoin_assumption).
		assert (rC > 0) as HrC by (apply reservecoin_assumption).
		assert (bC' > 0) as HbC' by (apply basecoin_assumption).
		assert (sC' > 0) as HsC' by (apply stablecoin_assumption).
		assert (rC' > 0) as HrC' by (apply reservecoin_assumption).
		assert (sP > 0) as HsP by (unfold sP; apply stablecoin_price_gt_0).
		assert (e0 > 0) as He0 by (apply exchangerate_assumption).
		assert (e1 > 0) as He1 by (apply exchangerate_assumption).
		assert (rP > 0) as HrP by (unfold rP; apply reservecoin_price_gt_0).
		assert (1 - fissFee > 0) as HfissFee by (apply Rgt_minus; rewrite H6; destruct fissionFee; simpl; lra).
		assert (bC + (1 - fissFee) * m > 0) as HbCNew.
		{
			apply Rplus_pos_pos; [auto |].
			apply Rmult_pos_pos; auto.
		}
		assert (alpha > 1) as Halphagtone.
		{
			unfold alpha. apply division_greater_than_one.
			- apply Rplus_gt_compat_l; rewrite <- Rmult_1_l with (r := m) at 1; 
			apply Rmult_gt_compat_r; [auto | apply Rgt_minus_pos; destruct fissionFee; simpl in H6; lra].
			- apply Rplus_pos_pos; [apply basecoin_assumption | apply Rmult_pos_pos; auto].
		}
		assert (alpha > 0) as Halpha.
		{
			unfold alpha. fold bC. apply Rdiv_pos_pos; 
			try (auto || apply Rplus_pos_pos; auto).
		}
		assert (fusRat > 0) as HfusRatgt0 by (unfold fusRat; apply fusion_ratio_gt_0).
		assert (1 - k * b0 > 0) as Hfeebound by (apply Rgt_minus; rewrite H4 in H16; rewrite <- H7 in H16; apply H16).
        rewrite <- H6. rewrite Rmult_1_r. rewrite Rmult_1_r.
        rewrite Rmult_div_swap with (r2 := sP).  
        rewrite Rmult_div_l with (r2 := sP); [| apply Rgt_not_eq; lra].
        (*
         * Proving that the stablecoin price before fission equals the target
         * price/exchange rate.
         *)
		replace sP with e0.
		2: {
			rewrite H2. unfold sP. destruct state_0 as [[[bC0 sC0 rC0] eR0] t0].
			apply eq_sym. 
			apply fusion_ratio_pegged_stablecoin_price_equals_target_price with 
            (s := sC0) (b := bC0) (e := eR0); try reflexivity.
            - apply reserve_ratio_gt_q_star_fusion_ratio_pegged; try reflexivity.
                + rewrite H5 in H12. apply H12.
		}
        (*
         * Proving that the stablecoin price before the beta decay equals the 
         * target price/exchange rate.
         *)
        replace sP' with e1.
        2: {
            unfold sP'. rewrite H3. apply eq_sym.
            apply fusion_ratio_pegged_stablecoin_price_equals_target_price with
            (s := sC') (e := e1) (b := bC'); auto;
            apply fission_reaction_preserves_pegged_state with 
            (timestamp := timestamp) (state0 := state_0) (m := m) (sC0 := sC) 
            (eR0 := e0) (bC0 := bC); auto; 
            apply reserve_ratio_gt_q_star_fusion_ratio_pegged; auto; 
            rewrite <- H5; auto.
        }
        rewrite H17.
		rewrite <- Rmult_plus_distr_r. rewrite Rdiv_mult_r_r; [| apply Rgt_not_eq; lra].
		replace rP' with (((1 - fusRat') * bC * alpha) / rC).
		2: {
			apply eq_sym. unfold rP'. unfold reservecoin_price. fold fusRat'.
			rewrite H1. unfold execute. unfold fission_reaction. 
			rewrite fission_output_alt. 
			simpl. rewrite <- H6. unfold reservecoin_price.
			unfold alpha. fold bC. fold rC.
			rewrite mult_div_assoc with (a := (1 - fusRat') * bC); try (apply Rgt_not_eq; auto).
			rewrite Rmult_assoc with (r1 := 1 - fusRat') (r2 := bC).
			rewrite Rmult_comm with (r1 := bC) (r2 := bC + m).
			rewrite <- Rmult_assoc with (r1 := 1 - fusRat') (r2 := bC + m).
			rewrite mul_div_eq_div_div with (a := (1 - fusRat') * (bC + m)); try (apply Rgt_not_eq); [| auto | apply Rmult_pos_pos; auto].
			rewrite Rmult_plus_distr_l with (r1 := rC).
			rewrite Rdiv_plus_distr. unfold Rdiv.
			rewrite Rmult_assoc with (r1 := rC) (r2 := bC).
			rewrite Rinv_r; [| apply Rgt_not_eq; auto]. rewrite Rmult_1_r.
			rewrite Rmult_comm with (r1 := m) (r2 := 1 - fissFee).
			rewrite Rmult_comm with (r1 := (1 - fissFee) * m) (r2 := rC).
			reflexivity.
		}
		(* Moving variables around through assert *)
		replace ((1 - fusRat) * (1 - fissFee) * (1 - betaDecayPosFeeVal) * ((1 - fusRat') * bC * alpha / rC))
		with ((1 - fissFee) * (1 - betaDecayPosFeeVal) * (1 - fusRat') * alpha * rP).
		2: {
			unfold rP; unfold reservecoin_price; subst fusRat;
			unfold bC; unfold rC; field_simplify; try reflexivity; apply Rgt_not_eq; apply reservecoin_assumption.
		} 
		rewrite <- Rmult_plus_distr_r. 
		rewrite <- Rmult_1_l with (r := rP) at 1. rewrite Rdiv_mult_r_r; [| apply Rgt_not_eq; auto].
		(* Moving variables around through assert *)
		replace ((1 - fissFee) * (1 - betaDecayPosFeeVal) * (1 - fusRat') * alpha) 
		with ((1 - betaDecayPosFeeVal) * (1 - fusRat') * alpha * (1 - fissFee)). 
		2: {
			field_simplify. reflexivity.
		}
		rewrite <- Rmult_plus_distr_r. rewrite Rmult_comm.
		(* Proving that (1 - fusRat') * alpha = fusRat * ((alpha * rr) - 1) *)
		assert (((1 - fusRat') * alpha) = (fusRat * ((alpha * rr) - 1))) as HfusRat'.
		{
			(* Proving that q* = q / alpha *)
			replace fusRat' with (fusRat / alpha).
			2: {
				unfold fusRat'. 
				rewrite fission_reaction_preserves_pegged_state with 
				(state0 := state_0) (timestamp := timestamp) (m := m) 
				(sC0 := sC) (eR0 := e0) (bC0 := bC) (sC1 := sC') 
				(eR1 := e1) (bC1 := bC'); try auto.
				- unfold execute in H1. unfold fission_reaction in H1.
				rewrite fission_output_alt in H1. fold bC in H1. 
				fold rC in H1. fold sC in H1.
				assert (get_basecoins (reactorState (stableCoinState state_1)) = bC + m) as H26.
				{
					rewrite H1; simpl; reflexivity.
				} 
				assert (get_stablecoins (reactorState (stableCoinState state_1)) = sC + m * (1 - extract_value fissionFee) * sC / bC) as H27.
				{
					rewrite H1; simpl; reflexivity.
				}
				assert (get_reservecoins (reactorState (stableCoinState state_1)) = rC + m * (1 - extract_value fissionFee) * rC / bC) as H28.
				{
					rewrite H1; simpl; reflexivity.
				}
				unfold sC'. unfold bC'. rewrite H27. rewrite H26.
				unfold fusRat. rewrite reserve_ratio_gt_q_star_fusion_ratio_pegged with (s := sC) (e := e0) (b := bC); try auto.
					+ unfold alpha. fold bC. rewrite H17. rewrite <- H6. field_simplify; try (repeat split); try (apply Rgt_not_eq; auto); apply Rplus_pos_pos; auto.
					+ lra.
				- apply reserve_ratio_gt_q_star_fusion_ratio_pegged; try (auto || lra).
			}
			rewrite Rmult_minus_distr_r. 
			rewrite Rmult_1_l. unfold Rdiv. rewrite Rmult_assoc.
			rewrite Rinv_l; [| apply Rgt_not_eq; auto].
			rewrite Rmult_1_r. rewrite sub_eq_mul_div_sub_one with (a := alpha) (b := fusRat); [| apply Rgt_not_eq; auto].
			unfold reserve_ratio in H5. fold fusRat in H5. unfold Rdiv. 
			rewrite <- Rdiv_1_l. rewrite H5. reflexivity.
		}
		rewrite Rmult_assoc with (r1 := 1 - betaDecayPosFeeVal). rewrite HfusRat'.
		(* Moving things around *)
		replace ((1 - fissFee) * (fusRat + (1 - betaDecayPosFeeVal) * (fusRat * (alpha * rr - 1)))) 
		with ((1 - fissFee) * (fusRat) * (1 + (1 - betaDecayPosFeeVal) * ((alpha * rr) - 1))).
		2: { field_simplify. reflexivity. }
		rewrite Rmult_comm. rewrite <- Rmult_assoc.
		rewrite a_div_b_mult_c_imp_a_mult_1_div_c_div_b.
		replace (1 / fusRat) with rr.
		(* Performing simplfications and substitutions *)
		rewrite Rmult_1_l. rewrite Rmult_comm. 
		rewrite Rmult_comm with (r1 := 1 - betaDecayPosFeeVal).
		rewrite H4. rewrite <- H7. rewrite Rminus_def with (r2 := 1). 
		rewrite Rminus_def with (r1 := rr / ((1 - fissFee) * (1 + (rr - 1) * (1 - k * b0)))).
		(* Proving the bound on the effective fee *)
		apply Rplus_lt_compat_r. apply b_gt_c_imp_a_div_b_lt_a_div_c.
			-- rewrite H5; apply reserve_ratio_gt_0.
			-- apply Rmult_pos_pos; [auto | apply Rplus_pos_pos]; try lra.
			apply Rmult_pos_pos; [apply Rgt_minus; rewrite H5; apply reserve_ratio_gt_1 | auto].
			-- apply Rmult_gt_compat_l; [auto |].
			apply Rplus_gt_compat_l. apply Rmult_gt_compat_r; [auto |].
			rewrite Rminus_def. rewrite Rminus_def. apply Rplus_gt_compat_r. 
			rewrite <- Rmult_1_l. apply Rmult_gt_compat_r; [rewrite H5; apply reserve_ratio_gt_0 | auto].				
    Qed.
End Theorem1.



