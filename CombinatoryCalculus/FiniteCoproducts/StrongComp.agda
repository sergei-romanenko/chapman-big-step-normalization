module FiniteCoproducts.StrongComp where

open import FiniteCoproducts.Utils
open import FiniteCoproducts.Syntax
open import FiniteCoproducts.BigStep

-- Strong Computability
SCN : ∀ {α} → Nf α → Set
SCN {⋆}     n = ⊤
SCN {α ⇒ β} f = ∀ a → SCN a → 
  Σ (Nf β) λ n →  (f ⟨∙⟩ a ⇓ n) × SCN n × (⌜ f ⌝ ∙ ⌜ a ⌝ ≈ ⌜ n ⌝)
SCN {Zero}     n = ⊥
SCN {α + β} (inlⁿ¹ x) = SCN x
SCN {α + β} (inrⁿ¹ x) = SCN x

SCC : ∀ {α β γ}(l : Nf (α ⇒ γ))(r : Nf (β ⇒ γ))(c : Nf (α + β)) →
      SCN l → SCN r → SCN c → 
      Σ (Nf γ) 
         λ n → (Cⁿ² l r ⟨∙⟩ c ⇓ n) × SCN n × (C ∙ ⌜ l ⌝ ∙ ⌜ r ⌝ ∙ ⌜ c ⌝ ≈ ⌜ n ⌝)
SCC l r (inlⁿ¹ x) sl sr sx = 
  proj₁ lx
    , (rCⁿ²ˡ (proj₁ (proj₂ lx)) , (proj₁ ∘ proj₂) (proj₂ lx) , ≈trans Cl ((proj₂ ∘ proj₂) (proj₂ lx))) 
  where lx = sl x sx
SCC l r (inrⁿ¹ x) sl sr sx = 
  proj₁ rx
    , (rCⁿ²ʳ (proj₁ (proj₂ rx)) , (proj₁ ∘ proj₂) (proj₂ rx) , ≈trans Cr ((proj₂ ∘ proj₂) (proj₂ rx))) 
  where rx = sr x sx

ZE : ⊥ → {X : Set} → X
ZE ()

all-scn : ∀ {α} → (n : Nf α) → SCN n
all-scn K0        = λ x sx → K1 x ,
                               (K0⇓ , (λ y sy → x , (K1⇓ , sx , ≈K)) , ≈refl)
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
all-scn (S1 x)   = λ y sy → S2 x y , (S1⇓ , (λ z sz → 
  let sx = all-scn x
      pxz = sx z sz
      pyz = sy z sz
      pxzyz = (proj₁ ∘ proj₂) (proj₂ pxz) (proj₁ pyz) ((proj₁ ∘ proj₂) (proj₂ pyz)) 
  in proj₁ pxzyz ,
          (S2⇓ (proj₁ (proj₂ pxz)) (proj₁ (proj₂ pyz)) (proj₁ (proj₂ pxzyz)) ,
              (proj₁ ∘ proj₂) (proj₂ pxzyz) ,
              ≈trans ≈S 
                     (≈trans (≈cong∙ ((proj₂ ∘ proj₂) (proj₂ pxz)) ((proj₂ ∘ proj₂) (proj₂ pyz)))
                            ((proj₂ ∘ proj₂) (proj₂ pxzyz))))) ,
  ≈refl)  
all-scn (S2 x y) = λ z sz →
  let sx = all-scn x
      sy = all-scn y
      pxz = sx z sz
      pyz = sy z sz
      pxzyz = (proj₁ ∘ proj₂) (proj₂ pxz) (proj₁ pyz) ((proj₁ ∘ proj₂) (proj₂ pyz)) 
  in proj₁ pxzyz ,
          (S2⇓ (proj₁ (proj₂ pxz)) (proj₁ (proj₂ pyz)) (proj₁ (proj₂ pxzyz)) ,
              (proj₁ ∘ proj₂) (proj₂ pxzyz) ,
              ≈trans ≈S 
                     (≈trans (≈cong∙ ((proj₂ ∘ proj₂) (proj₂ pxz)) ((proj₂ ∘ proj₂) (proj₂ pyz)))
                            ((proj₂ ∘ proj₂) (proj₂ pxzyz))))
all-scn NEⁿ = λ z sz → ZE sz 
all-scn (inlⁿ¹ x)  = all-scn x 
all-scn (inrⁿ¹ x)  = all-scn x 
all-scn inlⁿ = λ x sx → inlⁿ¹ x , rinl , sx , ≈refl
all-scn inrⁿ = λ x sx → inrⁿ¹ x , rinr , sx , ≈refl

all-scn Cⁿ        = λ l sl → 
  Cⁿ¹ l ,
      (rCⁿ ,
          (λ r sr → Cⁿ² l r , (rCⁿ¹ , (λ c sc → SCC l r c sl sr sc) , ≈refl)) ,
          ≈refl) 
all-scn (Cⁿ¹ l)   = λ r sr → 
  Cⁿ² l r , (rCⁿ¹ , (λ c sc → SCC l r c (all-scn l) sr sc) , ≈refl) 
all-scn (Cⁿ² l r) = λ c sc → SCC l r c (all-scn l) (all-scn r) sc 

SC : ∀ {α} → Tm α → Set
SC {α} t = Σ (Nf α) λ n → (t ⇓ n) × SCN n × (t ≈ ⌜ n ⌝)

all-sc : ∀ {α} → (t : Tm α) → SC t
all-sc K       = K0 , K⇓ , all-scn K0 , ≈refl
all-sc S       = S0 , S⇓ , all-scn S0 , ≈refl
all-sc (t ∙ u) with all-sc t          | all-sc u
all-sc (t ∙ u) | f , rf , sf , cf | a , ra , sa , ca with sf a sa
all-sc (t ∙ u) | f , rf , sf , cf | a , ra , sa , ca | v , rv , sv , cv
  = v , (A⇓ rf ra rv , sv , ≈trans (≈cong∙ cf ca) cv)
all-sc NE      = NEⁿ , rNE , (λ z sz → ZE sz) , ≈refl 
all-sc inl = inlⁿ , rinl , (λ x sx → inlⁿ¹ x , rinl , sx , ≈refl) , ≈refl
all-sc inr = inrⁿ , rinr , (λ x sx → inrⁿ¹ x , rinr , sx , ≈refl) , ≈refl
all-sc C       = 
  Cⁿ ,
      rC ,
          (λ l sl → Cⁿ¹ l ,
                        (rCⁿ ,
                            (λ r sr → Cⁿ² l r ,
                                          (rCⁿ¹ ,
                                              (λ c sc → SCC l r c sl sr sc) ,
                                              ≈refl)) ,
                            ≈refl)) ,
         ≈refl
