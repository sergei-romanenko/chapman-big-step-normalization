module BasicSystem.StrongComp where
open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.BigStep

-- Strong Computability
SCN : ∀ {σ} → Nf σ → Set
SCN {⋆}     n = ⊤
SCN {σ ⇒ τ} f = ∀ a → SCN a → 
  Σ (Nf τ) λ n →  (f ∙ⁿ a ⇓ n) × SCN n × (⌜ f ⌝ ∙ ⌜ a ⌝ ≈ ⌜ n ⌝)

-- there is a shorter proof of prop1 but the termination checker doesn't 
-- like it
prop1 : ∀ {σ} → (n : Nf σ) → SCN n
prop1 Kⁿ      = λ x sx → Kⁿ¹ x ,
                           rKⁿ , (λ y sy → x , rKⁿ¹ , sx , ≈K) , ≈refl
prop1 (Kⁿ¹ x) = λ y sy → x , (rKⁿ¹ , prop1 x , ≈K) 
prop1 Sⁿ      = λ x sx → Sⁿ¹ x ,
                           rSⁿ , 
                                   (λ y sy → Sⁿ² x y ,
                                                 rSⁿ¹ ,
                                                     (λ z sz → 
  let pxz = sx z sz
      pyz = sy z sz
      pxzyz = (proj₁ ∘ proj₂) (proj₂ pxz) (proj₁ pyz) ((proj₁ ∘ proj₂) (proj₂ pyz)) 
  in proj₁ pxzyz ,
      ((rSⁿ² (proj₁ (proj₂ pxz)) (proj₁ (proj₂ pyz)) (proj₁ (proj₂ pxzyz))) ,
          ((proj₁ ∘ proj₂) (proj₂ pxzyz)) ,
            (≈trans ≈S 
                    (≈trans (≈∙-cong ((proj₂ ∘ proj₂) (proj₂ pxz)) ((proj₂ ∘ proj₂) (proj₂ pyz)))
                      ((proj₂ ∘ proj₂) (proj₂ pxzyz)))))) , ≈refl) ,
  ≈refl
prop1 (Sⁿ¹ x)   = λ y sy → Sⁿ² x y , (rSⁿ¹ , (λ z sz → 
  let sx = prop1 x
      pxz = sx z sz
      pyz = sy z sz
      pxzyz = (proj₁ ∘ proj₂) (proj₂ pxz) (proj₁ pyz) ((proj₁ ∘ proj₂) (proj₂ pyz)) 
  in proj₁ pxzyz , 
      ((rSⁿ² (proj₁ (proj₂ pxz)) (proj₁ (proj₂ pyz)) (proj₁ (proj₂ pxzyz))) ,
              ((proj₁ ∘ proj₂) (proj₂ pxzyz)) ,
              (≈trans ≈S 
                     (≈trans (≈∙-cong ((proj₂ ∘ proj₂) (proj₂ pxz)) ((proj₂ ∘ proj₂) (proj₂ pyz)))
                            ((proj₂ ∘ proj₂) (proj₂ pxzyz)))))) ,
  ≈refl)  
prop1 (Sⁿ² x y) = λ z sz →
  let sx = prop1 x
      sy = prop1 y
      pxz = sx z sz
      pyz = sy z sz
      pxzyz = (proj₁ ∘ proj₂) (proj₂ pxz) (proj₁ pyz) ((proj₁ ∘ proj₂) (proj₂ pyz)) 
  in proj₁ pxzyz ,
      ((rSⁿ² (proj₁ (proj₂ pxz)) (proj₁ (proj₂ pyz)) (proj₁ (proj₂ pxzyz))) ,
          ((proj₁ ∘ proj₂) (proj₂ pxzyz)) ,
            (≈trans ≈S 
                    (≈trans (≈∙-cong ((proj₂ ∘ proj₂) (proj₂ pxz)) ((proj₂ ∘ proj₂) (proj₂ pyz)))
                      ((proj₂ ∘ proj₂) (proj₂ pxzyz)))))        

SC : ∀ {σ} → Tm σ → Set
SC {σ} t = Σ (Nf σ) λ n → (t ⇓ n) × SCN n × (t ≈ ⌜ n ⌝)

prop2 : ∀ {σ} → (t : Tm σ) → SC t
prop2 K       = Kⁿ , rK , prop1 Kⁿ , ≈refl
prop2 S       = Sⁿ , rS , prop1 Sⁿ , ≈refl
prop2 (t ∙ u) with prop2 t | prop2 u
prop2 (t ∙ u) | f , rf , sf , cf | a , ra , sa , ca with sf a sa
prop2 (t ∙ u) | f , rf , sf , cf | a , ra , sa , ca | v , rv , sv , cv
  = v , r∙ rf ra rv , sv , ≈trans (≈∙-cong cf ca) cv
