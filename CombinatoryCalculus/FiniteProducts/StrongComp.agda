module FiniteProducts.StrongComp where

open import FiniteProducts.Utils
open import FiniteProducts.Syntax
open import FiniteProducts.BigStep

-- Strong Computability
SCN : ∀ {α} → Nf α → Set
SCN {⋆}       n = ⊤
SCN {One}     n = ⊤
SCN {α ⇒ β} f = ∀ a → SCN a → 
  Σ (Nf β) λ n →  (f ⟨∙⟩ a ⇓ n) × SCN n × (⌜ f ⌝ ∙ ⌜ a ⌝ ≈ ⌜ n ⌝)
SCN {α * β} p = 
  (Σ (Nf α) λ n → (Fst0 ⟨∙⟩ p ⇓ n) × SCN n × (Fst ∙ ⌜ p ⌝ ≈ ⌜ n ⌝))
  ×
  (Σ (Nf β) λ n → (Snd0 ⟨∙⟩ p ⇓ n) × SCN n × (Snd ∙ ⌜ p ⌝ ≈ ⌜ n ⌝))


-- there is a shorter proof of all-scn but the termination checker doesn't 
-- like it
all-scn : ∀ {α} → (n : Nf α) → SCN n
all-scn K0        = λ x sx → K1 x ,
                                (K0⇓ , (λ y sy → x , (K1⇓ , sx , ≈K)) , ≈refl)
all-scn (K1 x)   = λ y sy → x , (K1⇓ , (all-scn x) , ≈K) 
all-scn S0        = λ x sx → S1 x ,
                               (S0⇓ , 
                                   (λ y sy → S2 x y ,
                                                 (S1⇓ ,
                                                     (λ z sz → 
  let pxz = sx z sz
      pyz = sy z sz
      pxzyz = (proj₁ ∘ proj₂) (proj₂ pxz) (proj₁ pyz) ((proj₁ ∘ proj₂) (proj₂ pyz)) 
  in proj₁ pxzyz ,
          ((S2⇓ (proj₁ (proj₂ pxz)) (proj₁ (proj₂ pyz)) (proj₁ (proj₂ pxzyz))) ,
              ((proj₁ ∘ proj₂) (proj₂ pxzyz)) ,
              (≈trans ≈S 
                     (≈trans (≈cong∙ ((proj₂ ∘ proj₂) (proj₂ pxz)) ((proj₂ ∘ proj₂) (proj₂ pyz)))
                            ((proj₂ ∘ proj₂) (proj₂ pxzyz)))))) , ≈refl)) ,
  ≈refl)
all-scn (S1 x)   = λ y sy → S2 x y , (S1⇓ , (λ z sz → 
  let sx = all-scn x
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
all-scn (S2 x y) = λ z sz →
  let sx = all-scn x
      sy = all-scn y
      pxz = sx z sz
      pyz = sy z sz
      pxzyz = (proj₁ ∘ proj₂) (proj₂ pxz) (proj₁ pyz) ((proj₁ ∘ proj₂) (proj₂ pyz)) 
  in proj₁ pxzyz ,
          ((S2⇓ (proj₁ (proj₂ pxz)) (proj₁ (proj₂ pyz)) (proj₁ (proj₂ pxzyz))) ,
              ((proj₁ ∘ proj₂) (proj₂ pxzyz)) ,
              (≈trans ≈S 
                     (≈trans (≈cong∙ ((proj₂ ∘ proj₂) (proj₂ pxz)) ((proj₂ ∘ proj₂) (proj₂ pyz)))
                            ((proj₂ ∘ proj₂) (proj₂ pxzyz)))))        
all-scn Void0      = record {} 
all-scn Pr0        = λ x sx → 
  Pr1 x ,
    (Pr0⇓ ,
      (λ y sy →
        Pr2 x y ,
          (Pr1⇓ , ((x , Fst0⇓ , sx , ≈Fst) , (y , Snd0⇓ , sy , ≈Snd)) , ≈refl))
        , ≈refl)
all-scn (Pr1 x)   = λ y sy → 
  Pr2 x y ,
    (Pr1⇓ , ((x , Fst0⇓ , all-scn x , ≈Fst) , (y , Snd0⇓ , sy , ≈Snd)) , ≈refl) 
all-scn (Pr2 x y) =
  (x , Fst0⇓ , all-scn x , ≈Fst) , (y , Snd0⇓ , all-scn y , ≈Snd)
all-scn Fst0      = λ _ → proj₁
all-scn Snd0      = λ _ → proj₂

SC : ∀ {α} → Tm α → Set
SC {α} t = Σ (Nf α) λ n → (t ⇓ n) × SCN n × (t ≈ ⌜ n ⌝)

all-sc : ∀ {α} → (t : Tm α) → SC t
all-sc K       = K0 , K⇓ , all-scn K0 , ≈refl
all-sc S       = S0 , S⇓ , all-scn S0 , ≈refl
all-sc (t ∙ u) with all-sc t          | all-sc u
all-sc (t ∙ u) | f , rf , sf , cf | a , ra , sa , ca with sf a sa
all-sc (t ∙ u) | f , rf , sf , cf | a , ra , sa , ca | v , rv , sv , cv
  = v , ((A⇓ rf ra rv) , sv , (≈trans (≈cong∙ cf ca) cv))
all-sc Void    = Void0 , (Void⇓ , (record {}) , ≈refl) 
all-sc Pr      = 
  Pr0 ,
    (Pr⇓ , 
      (λ x sx → Pr1 x ,
         (Pr0⇓ ,
           (λ y sy → Pr2 x y ,
              (Pr1⇓ ,
                ((x , Fst0⇓ , sx , ≈Fst) , (y , Snd0⇓ , sy , ≈Snd)) ,
                ≈refl)) ,
           ≈refl)) ,
      ≈refl) 
all-sc Fst     = Fst0 , (Fst⇓ , (λ _ → proj₁) , ≈refl) 
all-sc Snd     = Snd0 , (Snd⇓ , (λ _ → proj₂) , ≈refl) 
