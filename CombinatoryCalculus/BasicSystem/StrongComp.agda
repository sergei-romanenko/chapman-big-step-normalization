module BasicSystem.StrongComp where
open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.BigStep

-- Strong Computability
SCN : ∀ {α} → Nf α → Set
SCN {⋆}     n = ⊤
SCN {α ⇒ β} f = ∀ a → SCN a → 
  Σ (Nf β) λ n →  (f ⟨∙⟩ a ⇓ n) × SCN n × (⌜ f ⌝ ∙ ⌜ a ⌝ ≈ ⌜ n ⌝)

-- there is a shorter proof of prop1 but the termination checker doesn't 
-- like it
prop1 : ∀ {α} → (n : Nf α) → SCN n
prop1 K0      = λ x sx → K1 x ,
                           K0⇓ , (λ y sy → x , K1⇓ , sx , ≈K) , ≈refl
prop1 (K1 x) = λ y sy → x , (K1⇓ , prop1 x , ≈K) 
prop1 S0      = λ x sx → S1 x ,
                           S0⇓ , 
                                   (λ y sy → S2 x y ,
                                                 S1⇓ ,
                                                     (λ z sz → 
  let pxz = sx z sz
      pyz = sy z sz
      pxzyz = (proj₁ ∘ proj₂) (proj₂ pxz) (proj₁ pyz) ((proj₁ ∘ proj₂) (proj₂ pyz)) 
  in proj₁ pxzyz ,
      ((S2⇓ (proj₁ (proj₂ pxz)) (proj₁ (proj₂ pyz)) (proj₁ (proj₂ pxzyz))) ,
          ((proj₁ ∘ proj₂) (proj₂ pxzyz)) ,
            (≈trans ≈S 
                    (≈trans (≈cong∙ ((proj₂ ∘ proj₂) (proj₂ pxz)) ((proj₂ ∘ proj₂) (proj₂ pyz)))
                      ((proj₂ ∘ proj₂) (proj₂ pxzyz)))))) , ≈refl) ,
  ≈refl
prop1 (S1 x)   = λ y sy → S2 x y , (S1⇓ , (λ z sz → 
  let sx = prop1 x
      pxz = sx z sz
      pyz = sy z sz
      pxzyz = (proj₁ ∘ proj₂) (proj₂ pxz) (proj₁ pyz) ((proj₁ ∘ proj₂) (proj₂ pyz)) 
  in proj₁ pxzyz , 
      ((S2⇓ (proj₁ (proj₂ pxz)) (proj₁ (proj₂ pyz)) (proj₁ (proj₂ pxzyz))) ,
              ((proj₁ ∘ proj₂) (proj₂ pxzyz)) ,
              (≈trans ≈S 
                     (≈trans (≈cong∙ ((proj₂ ∘ proj₂) (proj₂ pxz)) ((proj₂ ∘ proj₂) (proj₂ pyz)))
                            ((proj₂ ∘ proj₂) (proj₂ pxzyz)))))) ,
  ≈refl)  
prop1 (S2 x y) = λ z sz →
  let sx = prop1 x
      sy = prop1 y
      pxz = sx z sz
      pyz = sy z sz
      pxzyz = (proj₁ ∘ proj₂) (proj₂ pxz) (proj₁ pyz) ((proj₁ ∘ proj₂) (proj₂ pyz)) 
  in proj₁ pxzyz ,
      ((S2⇓ (proj₁ (proj₂ pxz)) (proj₁ (proj₂ pyz)) (proj₁ (proj₂ pxzyz))) ,
          ((proj₁ ∘ proj₂) (proj₂ pxzyz)) ,
            (≈trans ≈S 
                    (≈trans (≈cong∙ ((proj₂ ∘ proj₂) (proj₂ pxz)) ((proj₂ ∘ proj₂) (proj₂ pyz)))
                      ((proj₂ ∘ proj₂) (proj₂ pxzyz)))))        

SC : ∀ {α} → Tm α → Set
SC {α} t = Σ (Nf α) λ n → (t ⇓ n) × SCN n × (t ≈ ⌜ n ⌝)

prop2 : ∀ {α} → (t : Tm α) → SC t
prop2 K       = K0 , K⇓ , prop1 K0 , ≈refl
prop2 S       = S0 , S⇓ , prop1 S0 , ≈refl
prop2 (t ∙ u) with prop2 t | prop2 u
prop2 (t ∙ u) | f , rf , sf , cf | a , ra , sa , ca with sf a sa
prop2 (t ∙ u) | f , rf , sf , cf | a , ra , sa , ca | v , rv , sv , cv
  = v , A⇓ rf ra rv , sv , ≈trans (≈cong∙ cf ca) cv
