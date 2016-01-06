module NaturalNumbers.StrongComp where

open import NaturalNumbers.Utils
open import NaturalNumbers.Syntax
open import NaturalNumbers.BigStep

-- Strong Computability
SCN : ∀ {α} → Nf α → Set
SCN {⋆}     n = ⊤
SCN {α ⇒ β} f = ∀ a → SCN a → 
  Σ (Nf β) λ n →  (f ⟨∙⟩ a ⇓ n) × SCN n × (⌜ f ⌝ ∙ ⌜ a ⌝ ≈ ⌜ n ⌝)
SCN {N}     n = ⊤

SCR : ∀ {α}(z : Nf α)(f : Nf (N ⇒ α ⇒ α))(n : Nf N) →
      SCN z → SCN f → 
      Σ (Nf α) 
        λ n' → (R2 z f ⟨∙⟩ n ⇓ n') × 
               SCN n' × 
               (R ∙ ⌜ z ⌝ ∙ ⌜ f ⌝ ∙ ⌜ n ⌝ ≈ ⌜ n' ⌝)  
SCR z f Zero0 sz sf = z , R2Z⇓ , sz , ≈RZero 
SCR z f (Suc1 n) sz sf  = 
  proj₁ fnrn ,
      (R2S⇓ (proj₁ (proj₂ fn)) (proj₁ (proj₂ rn)) (proj₁ (proj₂ fnrn)) ,
          (proj₁ ∘ proj₂) (proj₂ fnrn) ,
          ≈trans ≈RSuc (≈trans (≈cong∙ ((proj₂ ∘ proj₂) (proj₂ fn)) ((proj₂ ∘ proj₂) (proj₂ rn)))
                       ((proj₂ ∘ proj₂) (proj₂ fnrn))))
  where
  fn = sf n (record {})
  rn = SCR z f n sz sf
  fnrn = (proj₁ ∘ proj₂) (proj₂ fn) (proj₁ rn) ((proj₁ ∘ proj₂) (proj₂ rn)) 

all-scn : ∀ {α} → (n : Nf α) → SCN n
all-scn K0        = λ x sx → K1 x ,
                               K0⇓ , (λ y sy → x , K1⇓ , sx , ≈K) , ≈refl
all-scn (K1 x)   = λ y sy → x , (K1⇓ , all-scn x , ≈K) 
all-scn S0        = λ x sx → S1 x ,
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
all-scn (S1 x)   = λ y sy → S2 x y , S1⇓ , (λ z sz → 
  let sx = all-scn x
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
all-scn (S2 x y) = λ z sz →
  let sx = all-scn x
      sy = all-scn y
      pxz = sx z sz
      pyz = sy z sz
      pxzyz = (proj₁ ∘ proj₂) (proj₂ pxz) (proj₁ pyz) ((proj₁ ∘ proj₂) (proj₂ pyz)) 
  in proj₁ pxzyz ,
          S2⇓ (proj₁ (proj₂ pxz)) (proj₁ (proj₂ pyz)) (proj₁ (proj₂ pxzyz)) ,
              ((proj₁ ∘ proj₂) (proj₂ pxzyz)) ,
              ≈trans ≈S 
                     (≈trans (≈cong∙ ((proj₂ ∘ proj₂) (proj₂ pxz)) ((proj₂ ∘ proj₂) (proj₂ pyz)))
                             ((proj₂ ∘ proj₂) (proj₂ pxzyz)))
all-scn Zero0 = record {} 
all-scn Suc0 = λ n _ → Suc1 n , Suc0⇓ , record {} , ≈refl
all-scn (Suc1 n) = record {} 
all-scn R0 = λ z sz → 
  R1 z ,
      (R0⇓ ,
          (λ f sf → R2 z f ,
                          (R1⇓ ,
                              (λ n _ → SCR z f n sz sf) ,
                              ≈refl)) ,
          ≈refl)  
all-scn (R1 z) = λ f sf → 
  R2 z f ,
      R1⇓ ,
          (λ n _ → SCR z f n (all-scn z) sf) ,
          ≈refl
all-scn (R2 z f) = λ n _ → SCR z f n (all-scn z) (all-scn f) 

SC : ∀ {α} → Tm α → Set
SC {α} t = Σ (Nf α) λ n → (t ⇓ n) × SCN n × (t ≈ ⌜ n ⌝)

all-sc : ∀ {α} → (t : Tm α) → SC t
all-sc K       = K0 , K⇓ , all-scn K0 , ≈refl
all-sc S       = S0 , S⇓ , all-scn S0 , ≈refl
all-sc (t ∙ u) with all-sc t          | all-sc u
all-sc (t ∙ u) | f , rf , sf , cf | a , ra , sa , ca with sf a sa
all-sc (t ∙ u) | f , rf , sf , cf | a , ra , sa , ca | v , rv , sv , cv
  = v , A⇓ rf ra rv , sv , ≈trans (≈cong∙ cf ca) cv
all-sc Zero    = Zero0 , Zero⇓ , record {} , ≈refl
all-sc Suc     = 
  Suc0 ,
      Suc⇓ ,
          (λ n sn → Suc1 n ,
                        Suc0⇓ , record {} , ≈refl) ,
          ≈refl
all-sc R       = 
  R0 ,
      R⇓ ,
          (λ z sz → R1 z ,
                        R0⇓ ,
                            (λ f sf → R2 z f ,
                                          R1⇓ ,
                                              (λ n _ → SCR z f n sz sf) ,
                                              ≈refl) ,
                            ≈refl) ,
          ≈refl
