From StableCoinFormalization Require Export Datatypes.
From StableCoinFormalization Require Export HelperFunctions.
From StableCoinFormalization Require Export Functions.
Require Export Lra.
Local Open Scope R_scope.
Module Theorem1.
    Import Datatypes.
    Import HelperFunctions.
    Import Functions.
    Import Lra.

    Lemma actual_price_le_target_price_neutron :
        forall 
            (stableCoinState : StableCoinState),
            stablecoin_price (stableCoinState) <= target_price (stableCoinState).
        
        Proof.
            intros stableCoinState.
            destruct stableCoinState as [reactorState ex].
            destruct reactorState as [b s r].
            unfold stablecoin_price. unfold fusion_ratio. unfold target_price. 
            destruct qStar as [qs Hqs]. unfold Rmin. simpl.
            assert (b > 0 /\ r > 0 /\ s > 0) as H2.
            { apply reactorstate_assumption. }
            destruct H2 as [H2 [H3 H4]]. 
            destruct (Rle_dec qs (s * ex / b)).
            - apply Rmult_le_compat_r with (r := b) in r0 as H1.
            unfold Rdiv in H1. rewrite Rmult_assoc in H1. rewrite Rinv_l in H1.
            rewrite Rmult_1_r in H1.
            apply Rmult_le_compat_r with (r := / s) in H1.
            unfold Rdiv in H1. rewrite Rmult_assoc in H1. 
            rewrite Rmult_assoc in H1. assert (ex * / s = /s * ex).
            { rewrite Rmult_comm. reflexivity. } rewrite H in H1.
            rewrite <- Rmult_assoc in H1. rewrite <- Rmult_assoc in H1.
            rewrite Rinv_r in H1. rewrite Rmult_1_l in H1. apply H1.
            * nra.
            * apply Rlt_le. apply Rinv_0_lt_compat. apply H4.
            * nra.
            * apply Rlt_le. apply H2.
            - unfold Rdiv. rewrite Rmult_assoc with (r1 := s * ex).
            rewrite Rinv_l. rewrite Rmult_1_r. 
            rewrite Rmult_comm with (r1 := s * ex). rewrite <- Rmult_assoc.
            rewrite Rinv_l. rewrite Rmult_1_l.
            * nra.
            * nra.
            * nra.
        Qed.

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
            (state_0 : State)
            (state_1 : State) 
            (offer : Offer),
            is_valid_state (state_0) /\ is_valid_state (state_1) /\
            (1 / extract_value (qStar)) < 
            (reserve_ratio (state_0.(stableCoinState))) /\
            offer.(action) = SellStableCoin /\
            ((1 + get_effective_fee (timestamp) (state_0) (state_1) (BuyStableCoin)) * 
            target_price (state_0.(stableCoinState))) < 
            (offer.(value)) /\
            (get_effective_fee (timestamp) (state_0) (state_1) (BuyStableCoin) >= 0) /\
            stablecoin_price (state_0.(stableCoinState)) <> 0
            ->
            (get_rational_choice (BuyStableCoin) 
            (get_primary_market_offer (timestamp) (state_0) (state_1) (BuyStableCoin)) 
            (offer.(value)) = Secondary -> False) /\
            get_effective_fee (timestamp) (state_0) (state_1) (BuyStableCoin) = 
            ((reservecoin_price (state_0.(stableCoinState)) 
            * stablecoin_price (state_1.(stableCoinState))) / 
            ((fusion_ratio (state_0.(stableCoinState)) 
            * (1 - extract_value (fissionFee)) 
            * (reservecoin_price (state_0.(stableCoinState))) 
            * (stablecoin_price (state_1.(stableCoinState)))) + 
            ((1 - fusion_ratio (state_0.(stableCoinState))) 
            * (1 - extract_value (fissionFee)) 
            * (1 - beta_decay_pos_fee (state_1.(reactions)) (state_1.(stableCoinState)) (timestamp)) 
            * (reservecoin_price (state_1.(stableCoinState))) 
            * (stablecoin_price (state_0.(stableCoinState)))))) - 1.
    
    Proof.
        intros. split.
        - intros. destruct H as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]. 
        unfold get_primary_market_offer in H0.
        assert ((1 + get_effective_fee timestamp state_0 state_1 BuyStableCoin) * stablecoin_price (stableCoinState state_0) < value offer) as H8.
        { 
            apply Rle_lt_trans with (r2 := (1 + get_effective_fee timestamp state_0 state_1 BuyStableCoin) * target_price (stableCoinState state_0)). 
            apply Rmult_le_compat_l.
            apply Rplus_le_le_0_compat.
            - nra.
            - nra.
            - apply actual_price_le_target_price_neutron.
            - apply H5.
        } unfold get_rational_choice in H0. destruct Rlt_dec in H0. 
        * unfold get_effective_fee in H8. rewrite Rplus_comm with (r1 := 1) in H8.
        rewrite Rminus_def in H8.
        rewrite Rplus_assoc with (r2 := -1) in H8.
        assert (-1 + 1 = 0) as H9.
        { apply Rplus_opp_l. } rewrite H9 in H8. rewrite Rplus_0_r in H8.
        unfold Rdiv in H8. rewrite Rmult_assoc in H8. rewrite Rinv_l in H8. nra.
        apply H7.
        * discriminate H0.
        - unfold get_effective_fee. unfold base_coins_for_n_stable_coins.
        simpl. rewrite Rmult_1_r. rewrite Rmult_1_r.
        rewrite Rmult_div_swap with (r2 := stablecoin_price (stableCoinState state_0)).  
        rewrite Rmult_div_l with (r2 := stablecoin_price (stableCoinState state_0)).
        reflexivity. destruct H as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].
        apply H7.
    Qed.
    
End Theorem1.



