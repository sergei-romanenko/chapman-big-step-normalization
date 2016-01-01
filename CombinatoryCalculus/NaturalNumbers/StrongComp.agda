module NaturalNumbers.StrongComp where
open import NaturalNumbers.Utils
open import NaturalNumbers.Syntax
open import NaturalNumbers.BigStep

-- Strong Computability
SCN : ∀ {σ} → Nf σ → Set
SCN {⋆}     n = ⊤
SCN {N}     n = ⊤
SCN {σ ⇒ τ} f = ∀ a → SCN a → 
  Σ (Nf τ) λ n →  (f ∙ⁿ a ⇓ n) × SCN n × (⌜ f ⌝ ∙ ⌜ a ⌝ ≈ ⌜ n ⌝)

SCR : ∀ {σ}(z : Nf σ)(f : Nf (N ⇒ σ ⇒ σ))(n : Nf N) →
      SCN z → SCN f → 
      Σ (Nf σ) 
        λ n' → (Rⁿ² z f ∙ⁿ n ⇓ n') × 
               SCN n' × 
               (R ∙ ⌜ z ⌝ ∙ ⌜ f ⌝ ∙ ⌜ n ⌝ ≈ ⌜ n' ⌝)  
SCR z f zeroⁿ sz sf = z , rRⁿ²z , sz , ≈Rzero 
SCR z f (sucⁿ¹ n) sz sf  = 
  proj₁ fnrn ,
      (rRⁿ²f (proj₁ (proj₂ fn)) (proj₁ (proj₂ rn)) (proj₁ (proj₂ fnrn)) ,
          (proj₁ ∘ proj₂) (proj₂ fnrn) ,
          ≈trans ≈Rsuc (≈trans (≈∙-cong ((proj₂ ∘ proj₂) (proj₂ fn)) ((proj₂ ∘ proj₂) (proj₂ rn)))
                       ((proj₂ ∘ proj₂) (proj₂ fnrn))))
  where
  fn = sf n (record {})
  rn = SCR z f n sz sf
  fnrn = (proj₁ ∘ proj₂) (proj₂ fn) (proj₁ rn) ((proj₁ ∘ proj₂) (proj₂ rn)) 

prop1 : ∀ {σ} → (n : Nf σ) → SCN n
prop1 Kⁿ        = λ x sx → Kⁿ¹ x ,
                               rKⁿ , (λ y sy → x , rKⁿ¹ , sx , ≈K) , ≈refl
prop1 (Kⁿ¹ x)   = λ y sy → x , (rKⁿ¹ , prop1 x , ≈K) 
prop1 Sⁿ        = λ x sx → Sⁿ¹ x ,
                               (rSⁿ ,
                                   (λ y sy → Sⁿ² x y ,
                                                 (rSⁿ¹ ,
                                                     (λ z sz → 
  let pxz = sx z sz
      pyz = sy z sz
      pxzyz = (proj₁ ∘ proj₂) (proj₂ pxz) (proj₁ pyz) ((proj₁ ∘ proj₂) (proj₂ pyz)) 
  in proj₁ pxzyz ,
          (rSⁿ² (proj₁ (proj₂ pxz)) (proj₁ (proj₂ pyz)) (proj₁ (proj₂ pxzyz)) ,
              (proj₁ ∘ proj₂) (proj₂ pxzyz) ,
              ≈trans ≈S 
                     (≈trans (≈∙-cong ((proj₂ ∘ proj₂) (proj₂ pxz)) ((proj₂ ∘ proj₂) (proj₂ pyz)))
                             ((proj₂ ∘ proj₂) (proj₂ pxzyz))))) , ≈refl)) ,
  ≈refl)
prop1 (Sⁿ¹ x)   = λ y sy → Sⁿ² x y , rSⁿ¹ , (λ z sz → 
  let sx = prop1 x
      pxz = sx z sz
      pyz = sy z sz
      pxzyz = (proj₁ ∘ proj₂) (proj₂ pxz) (proj₁ pyz) ((proj₁ ∘ proj₂) (proj₂ pyz)) 
  in proj₁ pxzyz ,
          rSⁿ² (proj₁ (proj₂ pxz)) (proj₁ (proj₂ pyz)) (proj₁ (proj₂ pxzyz)) ,
              (proj₁ ∘ proj₂) (proj₂ pxzyz) ,
              ≈trans ≈S 
                     (≈trans (≈∙-cong ((proj₂ ∘ proj₂) (proj₂ pxz)) ((proj₂ ∘ proj₂) (proj₂ pyz)))
                             ((proj₂ ∘ proj₂) (proj₂ pxzyz)))) ,
  ≈refl
prop1 (Sⁿ² x y) = λ z sz →
  let sx = prop1 x
      sy = prop1 y
      pxz = sx z sz
      pyz = sy z sz
      pxzyz = (proj₁ ∘ proj₂) (proj₂ pxz) (proj₁ pyz) ((proj₁ ∘ proj₂) (proj₂ pyz)) 
  in proj₁ pxzyz ,
          rSⁿ² (proj₁ (proj₂ pxz)) (proj₁ (proj₂ pyz)) (proj₁ (proj₂ pxzyz)) ,
              ((proj₁ ∘ proj₂) (proj₂ pxzyz)) ,
              ≈trans ≈S 
                     (≈trans (≈∙-cong ((proj₂ ∘ proj₂) (proj₂ pxz)) ((proj₂ ∘ proj₂) (proj₂ pyz)))
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

SC : ∀ {σ} → Tm σ → Set
SC {σ} t = Σ (Nf σ) λ n → (t ⇓ n) × SCN n × (t ≈ ⌜ n ⌝)

prop2 : ∀ {σ} → (t : Tm σ) → SC t
prop2 K       = Kⁿ , rK , prop1 Kⁿ , ≈refl
prop2 S       = Sⁿ , rS , prop1 Sⁿ , ≈refl
prop2 (t ∙ u) with prop2 t          | prop2 u
prop2 (t ∙ u) | f , rf , sf , cf | a , ra , sa , ca with sf a sa
prop2 (t ∙ u) | f , rf , sf , cf | a , ra , sa , ca | v , rv , sv , cv
  = v , r∙ rf ra rv , sv , ≈trans (≈∙-cong cf ca) cv
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
