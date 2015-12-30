module FiniteProducts.StrongComp where
open import FiniteProducts.Utils
open import FiniteProducts.Syntax
open import FiniteProducts.BigStep

-- Strong Computability
SCN : ∀ {σ} → Nf σ → Set
SCN {ι}       n = True
SCN {One}     n = True
SCN {σ ⇒ τ} f = ∀ a → SCN a → 
  Σ (Nf τ) λ n →  (f ∙ⁿ a ⇓ n) ∧ SCN n ∧ (⌜ f ⌝ ∙ ⌜ a ⌝ ≈ ⌜ n ⌝)
SCN {σ × τ} p = 
  (Σ (Nf σ) λ n → (fstⁿ ∙ⁿ p ⇓ n) ∧ SCN n ∧ (fst ∙ ⌜ p ⌝ ≈ ⌜ n ⌝))
  ∧
  (Σ (Nf τ) λ n → (sndⁿ ∙ⁿ p ⇓ n) ∧ SCN n ∧ (snd ∙ ⌜ p ⌝ ≈ ⌜ n ⌝))



-- there is a shorter proof of prop1 but the termination checker doesn't 
-- like it
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
