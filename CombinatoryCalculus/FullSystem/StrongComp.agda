module FullSystem.StrongComp where
open import FullSystem.Utils
open import FullSystem.Syntax
open import FullSystem.BigStep

-- Strong Computability
SCN : ∀ {σ} → Nf σ → Set
SCN {ι}    n = True
SCN {N}    n = True
SCN {One}  n = True
SCN {Zero} n = False
SCN {σ ⇒ τ} f = ∀ a → SCN a → 
  Σ (Nf τ) λ n →  (f ∙ⁿ a ⇓ n) ∧ SCN n ∧ (⌜ f ⌝ ∙ ⌜ a ⌝ ≈ ⌜ n ⌝)
SCN {σ × τ} p = 
  (Σ (Nf σ) λ n → (fstⁿ ∙ⁿ p ⇓ n) ∧ SCN n ∧ (fst ∙ ⌜ p ⌝ ≈ ⌜ n ⌝))
  ∧
  (Σ (Nf τ) λ n → (sndⁿ ∙ⁿ p ⇓ n) ∧ SCN n ∧ (snd ∙ ⌜ p ⌝ ≈ ⌜ n ⌝))
SCN {σ + τ} (inlⁿ¹ x) = SCN x
SCN {σ + τ} (inrⁿ¹ x) = SCN x


SCC : ∀ {σ τ ρ}(l : Nf (σ ⇒ ρ))(r : Nf (τ ⇒ ρ))(c : Nf (σ + τ)) →
      SCN l → SCN r → SCN c → 
      Σ (Nf ρ) 
         λ n → (Cⁿ² l r ∙ⁿ c ⇓ n) ∧ SCN n ∧ (C ∙ ⌜ l ⌝ ∙ ⌜ r ⌝ ∙ ⌜ c ⌝ ≈ ⌜ n ⌝)
SCC l r (inlⁿ¹ x) sl sr sx = 
  proj₁ lx
    , (tr (rCⁿ²ˡ (π₀ (proj₂ lx))) (π₁ (proj₂ lx)) (≈trans Cl (π₂ (proj₂ lx)))) 
  where lx = sl x sx
SCC l r (inrⁿ¹ x) sl sr sx = 
  proj₁ rx
    , (tr (rCⁿ²ʳ (π₀ (proj₂ rx))) (π₁ (proj₂ rx)) (≈trans Cr (π₂ (proj₂ rx)))) 
  where rx = sr x sx

SCR : ∀ {σ}(z : Nf σ)(f : Nf (N ⇒ σ ⇒ σ))(n : Nf N) →
      SCN z → SCN f → 
      Σ (Nf σ) 
        λ n' → (Rⁿ² z f ∙ⁿ n ⇓ n') ∧ 
               SCN n' ∧ 
               (R ∙ ⌜ z ⌝ ∙ ⌜ f ⌝ ∙ ⌜ n ⌝ ≈ ⌜ n' ⌝)  
SCR z f zeroⁿ sz sf = z , (tr rRⁿ²z sz ≈Rzero) 
SCR z f (sucⁿ¹ n) sz sf  = 
  proj₁ fnrn ,
      (tr (rRⁿ²f (π₀ (proj₂ fn)) (π₀ (proj₂ rn)) (π₀ (proj₂ fnrn))) 
          (π₁ (proj₂ fnrn))
          (≈trans ≈Rsuc (≈trans (≈∙-cong (π₂ (proj₂ fn)) (π₂ (proj₂ rn))) (π₂ (proj₂ fnrn)))))
  where
  fn = sf n (record {})
  rn = SCR z f n sz sf
  fnrn = π₁ (proj₂ fn) (proj₁ rn) (π₁ (proj₂ rn)) 

ZE : False → {X : Set} → X
ZE ()

prop1 : ∀ {σ} → (n : Nf σ) → SCN n
prop1 Kⁿ        = λ x sx → Kⁿ¹ x ,
                               (tr rKⁿ (λ y sy → x , (tr rKⁿ¹ sx ≈K)) ≈refl)
prop1 (Kⁿ¹ x)   = λ y sy → x , (tr rKⁿ¹ (prop1 x) ≈K) 
prop1 Sⁿ        = λ x sx → Sⁿ¹ x ,
                               (tr rSⁿ 
                                   (λ y sy → Sⁿ² x y ,
                                                 (tr rSⁿ¹  
                                                     (λ z sz → 
  let pxz = sx z sz
      pyz = sy z sz
      pxzyz = π₁ (proj₂ pxz) (proj₁ pyz) (π₁ (proj₂ pyz)) 
  in proj₁ pxzyz ,
          (tr (rSⁿ² (π₀ (proj₂ pxz)) (π₀ (proj₂ pyz)) (π₀ (proj₂ pxzyz)))
              (π₁ (proj₂ pxzyz)) 
              (≈trans ≈S 
                     (≈trans (≈∙-cong (π₂ (proj₂ pxz)) (π₂ (proj₂ pyz)))
                            (π₂ (proj₂ pxzyz)))))) ≈refl)) 
  ≈refl)
prop1 (Sⁿ¹ x)   = λ y sy → Sⁿ² x y , (tr rSⁿ¹ (λ z sz → 
  let sx = prop1 x
      pxz = sx z sz
      pyz = sy z sz
      pxzyz = π₁ (proj₂ pxz) (proj₁ pyz) (π₁ (proj₂ pyz)) 
  in proj₁ pxzyz ,
          (tr (rSⁿ² (π₀ (proj₂ pxz)) (π₀ (proj₂ pyz)) (π₀ (proj₂ pxzyz)))
              (π₁ (proj₂ pxzyz)) 
              (≈trans ≈S 
                     (≈trans (≈∙-cong (π₂ (proj₂ pxz)) (π₂ (proj₂ pyz)))
                            (π₂ (proj₂ pxzyz)))))) 
  ≈refl)  
prop1 (Sⁿ² x y) = λ z sz →
  let sx = prop1 x
      sy = prop1 y
      pxz = sx z sz
      pyz = sy z sz
      pxzyz = π₁ (proj₂ pxz) (proj₁ pyz) (π₁ (proj₂ pyz)) 
  in proj₁ pxzyz ,
          (tr (rSⁿ² (π₀ (proj₂ pxz)) (π₀ (proj₂ pyz)) (π₀ (proj₂ pxzyz)))         
              (π₁ (proj₂ pxzyz)) 
              (≈trans ≈S 
                     (≈trans (≈∙-cong (π₂ (proj₂ pxz)) (π₂ (proj₂ pyz)))
                            (π₂ (proj₂ pxzyz)))))        
prop1 voidⁿ      = record {} 
prop1 prⁿ        = λ x sx → 
  prⁿ¹ x ,
      (tr rprⁿ 
          (λ y sy → prⁿ² x y ,
                        (tr rprⁿ¹ 
                            (pr (x , (tr rfstⁿ sx ≈fst)) 
                                (y , (tr rsndⁿ sy ≈snd))) 
                            ≈refl)) 
          ≈refl)  
prop1 (prⁿ¹ x)   = λ y sy → 
  prⁿ² x y ,
      (tr rprⁿ¹ 
          (pr (x , (tr rfstⁿ (prop1 x) ≈fst)) 
              (y , (tr rsndⁿ sy ≈snd))) 
          ≈refl) 
prop1 (prⁿ² x y) =
  pr (x , (tr rfstⁿ (prop1 x) ≈fst)) 
     (y , (tr rsndⁿ (prop1 y) ≈snd))
prop1 fstⁿ      = λ _ → pfst
prop1 sndⁿ      = λ _ → psnd
prop1 NEⁿ = λ z sz → ZE sz 
prop1 (inlⁿ¹ x)  = prop1 x 
prop1 (inrⁿ¹ x)  = prop1 x 
prop1 inlⁿ = λ x sx → inlⁿ¹ x , (tr rinl sx ≈refl)  
prop1 inrⁿ = λ x sx → inrⁿ¹ x , (tr rinr sx ≈refl) 

prop1 Cⁿ        = λ l sl → 
  Cⁿ¹ l ,
      (tr rCⁿ 
          (λ r sr → Cⁿ² l r , (tr rCⁿ¹ (λ c sc → SCC l r c sl sr sc) ≈refl))
          ≈refl) 
prop1 (Cⁿ¹ l)   = λ r sr → 
  Cⁿ² l r , (tr rCⁿ¹ (λ c sc → SCC l r c (prop1 l) sr sc) ≈refl) 
prop1 (Cⁿ² l r) = λ c sc → SCC l r c (prop1 l) (prop1 r) sc 
prop1 zeroⁿ = record {} 
prop1 sucⁿ = λ n _ → sucⁿ¹ n , (tr rsucⁿ (record {}) ≈refl ) 
prop1 (sucⁿ¹ n) = record {} 
prop1 Rⁿ = λ z sz → 
  Rⁿ¹ z , 
      (tr rRⁿ 
          (λ f sf → Rⁿ² z f ,
                          (tr rRⁿ¹
                              (λ n _ → SCR z f n sz sf)
                              ≈refl))
          ≈refl)  
prop1 (Rⁿ¹ z) = λ f sf → 
  Rⁿ² z f ,
      (tr rRⁿ¹ 
          (λ n _ → SCR z f n (prop1 z) sf) 
          ≈refl )  
prop1 (Rⁿ² z f) = λ n _ → SCR z f n (prop1 z) (prop1 f) 

SC : ∀ {σ} → Tm σ → Set
SC {σ} t = Σ (Nf σ) λ n → (t ⇓ n) ∧ SCN n ∧ (t ≈ ⌜ n ⌝)

prop2 : ∀ {σ} → (t : Tm σ) → SC t
prop2 K       = Kⁿ , (tr rK (prop1 Kⁿ) ≈refl) 
prop2 S       = Sⁿ , (tr rS (prop1 Sⁿ) ≈refl) 
prop2 (t ∙ u) with prop2 t          | prop2 u
prop2 (t ∙ u) | f , (tr rf sf cf) | a , (tr ra sa ca) with sf a sa
prop2 (t ∙ u) | f , (tr rf sf cf) | a , (tr ra sa ca) | v , (tr rv sv cv)
  = v , (tr (r∙ rf ra rv) sv (≈trans (≈∙-cong cf ca) cv))
prop2 void    = voidⁿ , (tr rvoid (record {}) ≈refl) 
prop2 pr      = 
  prⁿ ,
      (tr rpr 
          (λ x sx → prⁿ¹ x ,
                        (tr rprⁿ
                            (λ y sy → prⁿ² x y ,
                                          (tr rprⁿ¹  
                                              (pr (x , (tr rfstⁿ sx ≈fst)) 
                                                  (y , (tr rsndⁿ sy ≈snd)))
                                              ≈refl)) 
                            ≈refl))
          ≈refl ) 
prop2 fst     = fstⁿ , (tr rfst (λ _ → pfst) ≈refl) 
prop2 snd     = sndⁿ , (tr rsnd (λ _ → psnd) ≈refl) 
prop2 NE      = NEⁿ , (tr rNE (λ z sz → ZE sz) ≈refl) 
prop2 inl = inlⁿ , (tr rinl (λ x sx → inlⁿ¹ x , (tr rinl sx ≈refl)) ≈refl) 
prop2 inr = inrⁿ , (tr rinr (λ x sx → inrⁿ¹ x , (tr rinr sx ≈refl)) ≈refl) 
prop2 C       = 
  Cⁿ ,
      (tr rC 
          (λ l sl → Cⁿ¹ l ,
                        (tr rCⁿ 
                            (λ r sr → Cⁿ² l r ,
                                          (tr rCⁿ¹
                                              (λ c sc → SCC l r c sl sr sc) 
                                              ≈refl)) 
                            ≈refl)) 
         ≈refl)
prop2 zero    = zeroⁿ , (tr rzero (record {}) ≈refl)
prop2 suc     = 
  sucⁿ ,
      (tr rsuc 
          (λ n sn → sucⁿ¹ n ,
                        (tr rsucⁿ (record {}) ≈refl)) 
          ≈refl)
prop2 R       = 
  Rⁿ ,
      (tr rR  
          (λ z sz → Rⁿ¹ z ,
                        (tr rRⁿ  
                            (λ f sf → Rⁿ² z f ,
                                          (tr rRⁿ¹  
                                              (λ n _ → SCR z f n sz sf)
                                              ≈refl))
                            ≈refl))
          ≈refl)
