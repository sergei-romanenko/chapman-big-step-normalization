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
  (Σ (Nf α) λ n → (fstⁿ ⟨∙⟩ p ⇓ n) × SCN n × (fst ∙ ⌜ p ⌝ ≈ ⌜ n ⌝))
  ×
  (Σ (Nf β) λ n → (sndⁿ ⟨∙⟩ p ⇓ n) × SCN n × (snd ∙ ⌜ p ⌝ ≈ ⌜ n ⌝))


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
all-scn voidⁿ      = record {} 
all-scn prⁿ        = λ x sx → 
  prⁿ¹ x ,
    (rprⁿ ,
      (λ y sy →
        prⁿ² x y ,
          (rprⁿ¹ , ((x , rfstⁿ , sx , ≈fst) , (y , rsndⁿ , sy , ≈snd)) , ≈refl))
        , ≈refl)
all-scn (prⁿ¹ x)   = λ y sy → 
  prⁿ² x y ,
    (rprⁿ¹ , ((x , rfstⁿ , all-scn x , ≈fst) , (y , rsndⁿ , sy , ≈snd)) , ≈refl) 
all-scn (prⁿ² x y) =
  (x , rfstⁿ , all-scn x , ≈fst) , (y , rsndⁿ , all-scn y , ≈snd)
all-scn fstⁿ      = λ _ → proj₁
all-scn sndⁿ      = λ _ → proj₂

SC : ∀ {α} → Tm α → Set
SC {α} t = Σ (Nf α) λ n → (t ⇓ n) × SCN n × (t ≈ ⌜ n ⌝)

all-sc : ∀ {α} → (t : Tm α) → SC t
all-sc K       = K0 , K⇓ , all-scn K0 , ≈refl
all-sc S       = S0 , S⇓ , all-scn S0 , ≈refl
all-sc (t ∙ u) with all-sc t          | all-sc u
all-sc (t ∙ u) | f , rf , sf , cf | a , ra , sa , ca with sf a sa
all-sc (t ∙ u) | f , rf , sf , cf | a , ra , sa , ca | v , rv , sv , cv
  = v , ((A⇓ rf ra rv) , sv , (≈trans (≈cong∙ cf ca) cv))
all-sc void    = voidⁿ , (rvoid , (record {}) , ≈refl) 
all-sc pr      = 
  prⁿ ,
    (rpr , 
      (λ x sx → prⁿ¹ x ,
         (rprⁿ ,
           (λ y sy → prⁿ² x y ,
              (rprⁿ¹ ,
                ((x , rfstⁿ , sx , ≈fst) , (y , rsndⁿ , sy , ≈snd)) ,
                ≈refl)) ,
           ≈refl)) ,
      ≈refl) 
all-sc fst     = fstⁿ , (rfst , (λ _ → proj₁) , ≈refl) 
all-sc snd     = sndⁿ , (rsnd , (λ _ → proj₂) , ≈refl) 
