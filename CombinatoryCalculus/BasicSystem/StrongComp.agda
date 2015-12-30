module BasicSystem.StrongComp where
open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.BigStep

-- Strong Computability
SCN : ∀ {σ} → Nf σ → Set
SCN {ι}     n = True
SCN {σ ⇒ τ} f = ∀ a → SCN a → 
  Σ (Nf τ) λ n →  (f ∙ⁿ a ⇓ n) ∧ SCN n ∧ (⌜ f ⌝ ∙ ⌜ a ⌝ ≈ ⌜ n ⌝)

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

SC : ∀ {σ} → Tm σ → Set
SC {σ} t = Σ (Nf σ) λ n → (t ⇓ n) ∧ SCN n ∧ (t ≈ ⌜ n ⌝)

prop2 : ∀ {σ} → (t : Tm σ) → SC t
prop2 K       = Kⁿ , (tr rK (prop1 Kⁿ) ≈refl) 
prop2 S       = Sⁿ , (tr rS (prop1 Sⁿ) ≈refl) 
prop2 (t ∙ u) with prop2 t          | prop2 u
prop2 (t ∙ u) | f , (tr rf sf cf) | a , (tr ra sa ca) with sf a sa
prop2 (t ∙ u) | f , (tr rf sf cf) | a , (tr ra sa ca) | v , (tr rv sv cv)
  = v , (tr (r∙ rf ra rv) sv (≈trans (≈∙-cong cf ca) cv))
