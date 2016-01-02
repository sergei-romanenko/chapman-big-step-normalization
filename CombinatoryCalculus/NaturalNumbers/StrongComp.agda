module NaturalNumbers.StrongComp where
open import NaturalNumbers.Utils
open import NaturalNumbers.Syntax
open import NaturalNumbers.BigStep

-- Strong Computability
SCN : ∀ {α} → Nf α → Set
SCN {⋆}     n = ⊤
SCN {N}     n = ⊤
SCN {α ⇒ β} f = ∀ a → SCN a → 
  Σ (Nf β) λ n →  (f ⟨∙⟩ a ⇓ n) × SCN n × (⌜ f ⌝ ∙ ⌜ a ⌝ ≈ ⌜ n ⌝)

SCR : ∀ {α}(z : Nf α)(f : Nf (N ⇒ α ⇒ α))(n : Nf N) →
      SCN z → SCN f → 
      Σ (Nf α) 
        λ n' → (Rⁿ² z f ⟨∙⟩ n ⇓ n') × 
               SCN n' × 
               (R ∙ ⌜ z ⌝ ∙ ⌜ f ⌝ ∙ ⌜ n ⌝ ≈ ⌜ n' ⌝)  
SCR z f zeroⁿ sz sf = z , rRⁿ²z , sz , ≈Rzero 
SCR z f (sucⁿ¹ n) sz sf  = 
  proj₁ fnrn ,
      (rRⁿ²f (proj₁ (proj₂ fn)) (proj₁ (proj₂ rn)) (proj₁ (proj₂ fnrn)) ,
          (proj₁ ∘ proj₂) (proj₂ fnrn) ,
          ≈trans ≈Rsuc (≈trans (≈cong∙ ((proj₂ ∘ proj₂) (proj₂ fn)) ((proj₂ ∘ proj₂) (proj₂ rn)))
                       ((proj₂ ∘ proj₂) (proj₂ fnrn))))
  where
  fn = sf n (record {})
  rn = SCR z f n sz sf
  fnrn = (proj₁ ∘ proj₂) (proj₂ fn) (proj₁ rn) ((proj₁ ∘ proj₂) (proj₂ rn)) 

prop1 : ∀ {α} → (n : Nf α) → SCN n
prop1 K0        = λ x sx → K1 x ,
                               K0⇓ , (λ y sy → x , K1⇓ , sx , ≈K) , ≈refl
prop1 (K1 x)   = λ y sy → x , (K1⇓ , prop1 x , ≈K) 
prop1 S0        = λ x sx → S1 x ,
                               (S0⇓ ,
                                   (λ y sy → S2 x y ,
                                                 (S1⇓ ,
                                                     (λ z sz → 
  let pxz = sx z sz
      pyz = sy z sz
      pxzyz = (proj₁ ∘ proj₂) (proj₂ pxz) (proj₁ pyz) ((proj₁ ∘ proj₂) (proj₂ pyz)) 
  in proj₁ pxzyz ,
          (S2⇓ (proj₁ (proj₂ pxz)) (proj₁ (proj₂ pyz)) (proj₁ (proj₂ pxzyz)) ,
              (proj₁ ∘ proj₂) (proj₂ pxzyz) ,
              ≈trans ≈S 
                     (≈trans (≈cong∙ ((proj₂ ∘ proj₂) (proj₂ pxz)) ((proj₂ ∘ proj₂) (proj₂ pyz)))
                             ((proj₂ ∘ proj₂) (proj₂ pxzyz))))) , ≈refl)) ,
  ≈refl)
prop1 (S1 x)   = λ y sy → S2 x y , S1⇓ , (λ z sz → 
  let sx = prop1 x
      pxz = sx z sz
      pyz = sy z sz
      pxzyz = (proj₁ ∘ proj₂) (proj₂ pxz) (proj₁ pyz) ((proj₁ ∘ proj₂) (proj₂ pyz)) 
  in proj₁ pxzyz ,
          S2⇓ (proj₁ (proj₂ pxz)) (proj₁ (proj₂ pyz)) (proj₁ (proj₂ pxzyz)) ,
              (proj₁ ∘ proj₂) (proj₂ pxzyz) ,
              ≈trans ≈S 
                     (≈trans (≈cong∙ ((proj₂ ∘ proj₂) (proj₂ pxz)) ((proj₂ ∘ proj₂) (proj₂ pyz)))
                             ((proj₂ ∘ proj₂) (proj₂ pxzyz)))) ,
  ≈refl
prop1 (S2 x y) = λ z sz →
  let sx = prop1 x
      sy = prop1 y
      pxz = sx z sz
      pyz = sy z sz
      pxzyz = (proj₁ ∘ proj₂) (proj₂ pxz) (proj₁ pyz) ((proj₁ ∘ proj₂) (proj₂ pyz)) 
  in proj₁ pxzyz ,
          S2⇓ (proj₁ (proj₂ pxz)) (proj₁ (proj₂ pyz)) (proj₁ (proj₂ pxzyz)) ,
              ((proj₁ ∘ proj₂) (proj₂ pxzyz)) ,
              ≈trans ≈S 
                     (≈trans (≈cong∙ ((proj₂ ∘ proj₂) (proj₂ pxz)) ((proj₂ ∘ proj₂) (proj₂ pyz)))
                             ((proj₂ ∘ proj₂) (proj₂ pxzyz)))
prop1 zeroⁿ = record {} 
prop1 sucⁿ = λ n _ → sucⁿ¹ n , rsucⁿ , record {} , ≈refl
prop1 (sucⁿ¹ n) = record {} 
prop1 Rⁿ = λ z sz → 
  Rⁿ¹ z ,
      (rRⁿ ,
          (λ f sf → Rⁿ² z f ,
                          (rRⁿ¹ ,
                              (λ n _ → SCR z f n sz sf) ,
                              ≈refl)) ,
          ≈refl)  
prop1 (Rⁿ¹ z) = λ f sf → 
  Rⁿ² z f ,
      rRⁿ¹ ,
          (λ n _ → SCR z f n (prop1 z) sf) ,
          ≈refl
prop1 (Rⁿ² z f) = λ n _ → SCR z f n (prop1 z) (prop1 f) 

SC : ∀ {α} → Tm α → Set
SC {α} t = Σ (Nf α) λ n → (t ⇓ n) × SCN n × (t ≈ ⌜ n ⌝)

prop2 : ∀ {α} → (t : Tm α) → SC t
prop2 K       = K0 , K⇓ , prop1 K0 , ≈refl
prop2 S       = S0 , S⇓ , prop1 S0 , ≈refl
prop2 (t ∙ u) with prop2 t          | prop2 u
prop2 (t ∙ u) | f , rf , sf , cf | a , ra , sa , ca with sf a sa
prop2 (t ∙ u) | f , rf , sf , cf | a , ra , sa , ca | v , rv , sv , cv
  = v , A⇓ rf ra rv , sv , ≈trans (≈cong∙ cf ca) cv
prop2 zero    = zeroⁿ , rzero , record {} , ≈refl
prop2 suc     = 
  sucⁿ ,
      rsuc ,
          (λ n sn → sucⁿ¹ n ,
                        rsucⁿ , record {} , ≈refl) ,
          ≈refl
prop2 R       = 
  Rⁿ ,
      rR ,
          (λ z sz → Rⁿ¹ z ,
                        rRⁿ ,
                            (λ f sf → Rⁿ² z f ,
                                          rRⁿ¹ ,
                                              (λ n _ → SCR z f n sz sf) ,
                                              ≈refl) ,
                            ≈refl) ,
          ≈refl
