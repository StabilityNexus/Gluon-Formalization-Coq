From StableCoinFormalization Require Export Datatypes.
From StableCoinFormalization Require Export HelperFunctions.
From StableCoinFormalization Require Export Functions.
From StableCoinFormalization Require Export HelperLemmas.
Require Export Lqa.
Require Export Lia.

Module Theorem2.
    Import Datatypes.
    Import HelperFunctions.
    Import HelperLemmas.
    Import Functions.
    Import Qminmax.
    Import QArith.
    Import Lqa.
    Import Lia.

    Lemma actual_price_le_target_price_neutron :
        forall 
            (stableCoinState : StableCoinState),
            neutron_price (stableCoinState) <= target_price (stableCoinState).
        
        Proof.
            intros stableCoinState. 
            destruct stableCoinState as [reactorState exchangeRate].
            destruct reactorState as [nuclei neutrons protons].
            destruct nuclei as [nu Hnu]. destruct neutrons as [n Hn]. 
            destruct protons as [p Hp]. destruct exchangeRate as [ex Hex].
            unfold neutron_price. unfold fusion_ratio. unfold target_price. 
            simpl. destruct qStar as [qs Hqs]. simpl. 
            destruct (Q.min_spec (qs) (n * ex / nu)) as [] eqn:E. 
            - destruct a as [H1 H2]. rewrite H2. unfold Qdiv.
            apply Qmult_lt_compat_r with (z:=nu) in H1 as H3.
            unfold Qdiv in H3.
            rewrite <- Qmult_assoc in H3.
            assert (/nu * nu == nu * / nu) as H4.
            { apply Qmult_comm. }
            rewrite H4 in H3. rewrite Qmult_inv_r in H3. 
            rewrite Qmult_1_r in H3.
            apply Qmult_lt_compat_r with (z:=/n) in H3.
            rewrite <- Qmult_assoc in H3.
            rewrite <- Qmult_assoc in H3.
            assert (ex * /n == /n * ex ) as H5.
            { apply Qmult_comm. }
            rewrite H5 in H3. rewrite Qmult_assoc in H3.
            rewrite Qmult_assoc in H3. rewrite Qmult_inv_r in H3.
            rewrite Qmult_1_l in H3. apply Qlt_le_weak. apply H3.
            apply Qnot_eq_sym. apply Qlt_not_eq. apply Hn. 
            apply Qinv_lt_0_compat. apply Hn.
            apply Qnot_eq_sym. apply Qlt_not_eq. apply Hnu.
            apply Hnu.
            - destruct a as [H1 H2]. rewrite H2. unfold Qdiv.
            simpl. rewrite <- Qmult_assoc with (m:=/nu). 
            rewrite Qmult_comm with (x:=/nu). rewrite Qmult_inv_r.
            rewrite <- Qmult_assoc. rewrite Qmult_1_l. rewrite <- Qmult_assoc.
            rewrite <- Qmult_comm. rewrite <- Qmult_assoc.
            assert (/ n * n == n * / n).
            { rewrite Qmult_comm. reflexivity. }
            rewrite H. rewrite Qmult_inv_r. rewrite Qmult_1_r. apply Qle_refl.
            apply Qnot_eq_sym. apply Qlt_not_eq. apply Hn.
            apply Qnot_eq_sym. apply Qlt_not_eq. apply Hnu.
        Qed.

    

    Theorem peg_maintenance_lower_bound :
        forall
            (timestamp : nat) 
            (state_0 : State)
            (state_1 : State) 
            (offer : Offer),
            (1 / extract_value (qStar)) < 
            (reserve_ratio (state_0.(stableCoinState))) /\
            offer.(action) = BuyStableCoin /\
            ((1 - get_effective_fee (timestamp) (state_0) (state_1) (SellStableCoin)) * 
            target_price (state_0.(stableCoinState))) > 
            (extract_value (offer.(value))) /\
            (get_effective_fee (timestamp) (state_0) (state_1) (SellStableCoin) >= 0)
            ->
            (get_rational_choice (SellStableCoin) 
            (get_primary_market_offer (timestamp) (state_0) (state_1) (SellStableCoin)) 
            (extract_value (offer.(value))) = Secondary -> False) /\
            get_effective_fee (timestamp) (state_0) (state_1) (SellStableCoin) <=
            (1 - (1 - extract_value (fusionFee)) * (1 - beta_decay_neg_fee (state_0) (timestamp))).
    
    Proof.
        intros. split.
        - intros. destruct H as [H1 [H2 [H3 H4]]]. rewrite Qmult_comm in H3.
          apply Qle_lt_trans with 
          (x:= (1 + get_effective_fee timestamp state_0 state_1 BuyStableCoin) * 
          neutron_price (state_0.(stableCoinState))) in H3.
          simpl in H0. rewrite Qgt_alt in H3. simpl in H3. rewrite H3 in H0. 
          discriminate H0. rewrite Qmult_comm. apply Qmult_le_compat_r.
          * apply actual_price_le_target_price_neutron.
          * apply nonnegative_plus_nonnegative.
            + unfold Qle. simpl. lia.
            + apply H4.
        -  
    Qed.
    
End Theorem1.



