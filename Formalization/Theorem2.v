From StableCoinFormalization Require Export Datatypes.
From StableCoinFormalization Require Export HelperFunctions.
From StableCoinFormalization Require Export Functions.
From StableCoinFormalization Require Export FunctionProofs.
From StableCoinFormalization Require Export HelperLemmas.
Require Export Lra.
Local Open Scope R_scope.
Module Theorem2.
    Import Datatypes.
    Import HelperFunctions.
    Import Functions.
    Import Lra.
    Import FunctionProofs.
    Import HelperLemmas.

    Theorem peg_maintenance_lower_bound :
    forall
        (timestamp : nat) 
        (state_0 state_1 : State) 
        (offer : Offer)    
        (primaryMarketOffer secondaryMarketOffer sC e0 e1 b0 rr k 
		betaDecayNegFeeVal effFee gamma q fusFee s_0 p_s_0 : R),
    (state_1 = execute (state_0) (BetaDecayNegEvent (sC)) (timestamp)) ->
	(q = fusion_ratio (state_0.(stableCoinState))) ->
	(fusFee = extract_value (fusionFee)) ->
	(s_0 = get_stablecoins (state_0.(stableCoinState).(reactorState))) ->
	(s_0 > 1) ->
	(p_s_0 = stablecoin_price (state_0.(stableCoinState))) ->
    (e0 = target_price (state_0.(stableCoinState))) ->
    (e1 = target_price (state_1.(stableCoinState))) ->
	(e0 = e1) ->
	(b0 = extract_value (betaDecayFee0)) ->
	(rr = reserve_ratio (state_0.(stableCoinState))) ->
	(rr > /extract_value (qStar)) ->
	(k > 0) ->
    (betaDecayNegFeeVal = k * b0) ->
	(betaDecayNegFeeVal < 1) ->
	(effFee = get_effective_fee (timestamp) (state_0) (state_1) (gamma) (betaDecayNegFeeVal) (SellStableCoin)) ->
	(offer.(action) = BuyStableCoin) ->
    (primaryMarketOffer = get_primary_market_offer (timestamp) (state_0) (state_1) (gamma) (betaDecayNegFeeVal) (SellStableCoin)) ->
    (secondaryMarketOffer = offer.(value)) ->
    (((1 - effFee) * target_price (state_0.(stableCoinState))) > (secondaryMarketOffer)) -> 
	(gamma = ((1 - q) * s_0) / (((s_0 - 1) * (1 - betaDecayNegFeeVal) * q) + ((1 - q) * s_0))) ->  
    (get_rational_choice (SellStableCoin) (primaryMarketOffer) (secondaryMarketOffer) = Primary) /\
	(effFee = 1 - (((1 - fusFee) * (1 - betaDecayNegFeeVal)) / (1 - (q * betaDecayNegFeeVal)))).
    Proof.
		intros 
		timestamp state_0 state_1 offer primaryMarketOffer 
		secondaryMarketOffer sC e0 e1 b0 rr k betaDecayNegFeeVal effFee gamma q 
		fusFee s_0 p_s_0
		Hs1s0 HqVal HfusFeeVal Hs_0Val Hs_0_gt_1 Hp_s_0Val He0val He1val He0e1 
		Hb0val Hrrval Hrrrange Hkrange Hbetaval Hbetarange 
		Hefffeeval Hofferaction Hpmo Hsmo Hsmorange Hgamma.
		(*
		 * Useful asserts
		 *)
		assert (stablecoin_price (state_0.(stableCoinState)) = 
		target_price (state_0.(stableCoinState))) as HscPtP.
		{
			rewrite fusion_ratio_pegged_stablecoin_price_equals_target_price with 
			(s := get_stablecoins (state_0.(stableCoinState).(reactorState))) 
			(e := target_price (state_0.(stableCoinState))) 
			(b := get_basecoins (state_0.(stableCoinState).(reactorState))); auto.
			rewrite reserve_ratio_gt_q_star_fusion_ratio_pegged with
			(s := get_stablecoins (state_0.(stableCoinState).(reactorState))) 
			(e := target_price (state_0.(stableCoinState))) 
			(b := get_basecoins (state_0.(stableCoinState).(reactorState))); auto.
			rewrite Hrrval in Hrrrange. apply Hrrrange.
		}
		split.
		(*
         * Proving that choosing the secondary market for buying stable coins
         * is an irrational choice
         *)
		- unfold get_rational_choice. destruct Rgt_dec.
            + assert (primaryMarketOffer > secondaryMarketOffer).
            {
                rewrite Hpmo, Hsmo. unfold get_primary_market_offer.
				rewrite HscPtP. rewrite Hefffeeval, Hsmo in Hsmorange.
				apply Hsmorange.
            } lra.
            + reflexivity.
		(*
		 * Proving the value of the effective fee
		 *)
		-
		(*
		 * Proving required asserts
		 *)
		assert (p_s_0 > 0) as Hps0gt1 by (rewrite Hp_s_0Val; apply stablecoin_price_gt_0).
		assert (betaDecayNegFeeVal > 0) as Hbetavalgt0. 
		{
			rewrite Hbetaval, Hb0val. destruct betaDecayFee0. simpl.
			apply Rmult_pos_pos; lra.
		}
		assert (p_s_0 <> 0) as Hps0ne0 by (apply Rgt_not_eq; apply Hps0gt1).
		assert ((s_0 - 1) * (1 - betaDecayNegFeeVal) * q + (1 - q) * s_0 <> 0) as Hdenomnonzero.
		{
			apply Rgt_not_eq. apply Rplus_pos_pos.
			- repeat apply Rmult_pos_pos; [try lra | try lra | rewrite HqVal; apply fusion_ratio_gt_0]. 
			- repeat apply Rmult_pos_pos; [apply Rgt_minus; rewrite HqVal; apply fusion_ratio_lt_1 | lra].
		}
		assert ((1 - betaDecayNegFeeVal) * q + (1 - q) <> 0) as Hbetadecayq.
		{
			apply Rgt_not_eq; apply Rplus_pos_pos; try apply Rmult_pos_pos; 
			try apply Rgt_minus; try rewrite HqVal; 
			try apply fusion_ratio_lt_1; try apply fusion_ratio_gt_0; try lra.
		}
		assert (1 - gamma = ((s_0 - 1) * (1 - betaDecayNegFeeVal) * (q)) / (((s_0 - 1) * (1 - betaDecayNegFeeVal) * (q)) + ((1 - q) * (s_0)))) as H1minusgamma.
		{
			rewrite Hgamma. field_simplify; auto.
		}
		assert (1 - (gamma / s_0) = ((s_0 - 1) * (((1 - betaDecayNegFeeVal) * (q)) + (1 - q))) / (((s_0 - 1) * (1 - betaDecayNegFeeVal) * (q)) + ((1 - q) * (s_0)))) as H1minusgammadivs0.
		{
			rewrite Hgamma. field_simplify; [reflexivity | auto | split; try lra].
		}
		assert ((1 - gamma) / (1 - (gamma / s_0)) = (((1 - betaDecayNegFeeVal) * q) / (1 - (q * betaDecayNegFeeVal)))) as Hgammasimpl.
		{
			rewrite H1minusgamma, H1minusgammadivs0; field_simplify; try lra.
		}
		rewrite Hefffeeval. unfold get_effective_fee. 
		unfold base_coins_from_n_stable_coins. 
		rewrite <- HfusFeeVal, <- Hs_0Val, <- Hp_s_0Val, <- HqVal. 
		repeat rewrite Rmult_1_r.
		rewrite Rmult_div_swap with (r1 := (1 - fusFee) * (1 - gamma)) 
		(r2 := p_s_0).
		rewrite Rmult_div_l; try auto.
		rewrite a_mult_b_div_c_mult_b_eq_a_div_c_mult_b_div_d with
		(a := 1 - fusFee) (b := 1 - gamma) (c := q) (d := 1 - gamma / s_0).
		rewrite Hgammasimpl; field_simplify; repeat split; try lra; 
		try apply Rgt_not_eq. try rewrite HqVal; try apply fusion_ratio_gt_0. 
    Qed.
End Theorem2.



