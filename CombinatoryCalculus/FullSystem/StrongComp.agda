module FullSystem.StrongComp where

open import FullSystem.Utils
open import FullSystem.Syntax
open import FullSystem.BigStep

-- Strong Computability
SCN : ∀ {α} → Nf α → Set
SCN {⋆}    n = ⊤
SCN {N}    n = ⊤
SCN {One}  n = ⊤
SCN {Zero} n = ⊥
SCN {α ⇒ β} f = ∀ a → SCN a → 
  Σ (Nf β) λ n → (f ⟨∙⟩ a ⇓ n) × SCN n × (⌜ f ⌝ ∙ ⌜ a ⌝ ≈ ⌜ n ⌝)
SCN {α * β} p = 
  (Σ (Nf α) λ n → (Fst0 ⟨∙⟩ p ⇓ n) × SCN n × (Fst ∙ ⌜ p ⌝ ≈ ⌜ n ⌝))
  ×
  (Σ (Nf β) λ n → (Snd0 ⟨∙⟩ p ⇓ n) × SCN n × (Snd ∙ ⌜ p ⌝ ≈ ⌜ n ⌝))
SCN {α + β} (Inl1 x) = SCN x
SCN {α + β} (Inr1 x) = SCN x


all-scn-C3 : ∀ {α β γ}(l : Nf (α ⇒ γ))(r : Nf (β ⇒ γ))(c : Nf (α + β)) →
      SCN l → SCN r → SCN c → 
      Σ (Nf γ) 
         λ n → (C2 l r ⟨∙⟩ c ⇓ n) × SCN n × (C ∙ ⌜ l ⌝ ∙ ⌜ r ⌝ ∙ ⌜ c ⌝ ≈ ⌜ n ⌝)
all-scn-C3 l r (Inl1 x) sl sr sx = 
  proj₁ lx
    , C2L⇓ (proj₁ (proj₂ lx)) , (proj₁ ∘ proj₂) (proj₂ lx) , ≈trans Cl ((proj₂ ∘ proj₂) (proj₂ lx))
  where lx = sl x sx
all-scn-C3 l r (Inr1 x) sl sr sx = 
  proj₁ rx
    , C2R⇓ (proj₁ (proj₂ rx)) , (proj₁ ∘ proj₂) (proj₂ rx) , ≈trans Cr ((proj₂ ∘ proj₂) (proj₂ rx))
  where rx = sr x sx

SCR : ∀ {α}(z : Nf α)(f : Nf (N ⇒ α ⇒ α))(n : Nf N) →
      SCN z → SCN f → 
      Σ (Nf α) 
        λ n' → (Rⁿ² z f ⟨∙⟩ n ⇓ n') × 
               SCN n' ×
               (R ∙ ⌜ z ⌝ ∙ ⌜ f ⌝ ∙ ⌜ n ⌝ ≈ ⌜ n' ⌝)  
SCR z f zeroⁿ sz sf = z , rRⁿ²z , sz , ≈Rzero
SCR z f (sucⁿ¹ n) sz sf  = 
  proj₁ fnrn ,
      rRⁿ²f (proj₁ (proj₂ fn)) (proj₁ (proj₂ rn)) (proj₁ (proj₂ fnrn)) ,
          (proj₁ ∘ proj₂) (proj₂ fnrn) ,
          ≈trans ≈Rsuc (≈trans (≈cong∙ ((proj₂ ∘ proj₂) (proj₂ fn)) ((proj₂ ∘ proj₂) (proj₂ rn)))
                                ((proj₂ ∘ proj₂) (proj₂ fnrn)))
  where
  fn = sf n (record {})
  rn = SCR z f n sz sf
  fnrn = (proj₁ ∘ proj₂) (proj₂ fn) (proj₁ rn) ((proj₁ ∘ proj₂) (proj₂ rn)) 

ZE : ⊥ → {X : Set} → X
ZE ()

all-scn : ∀ {α} → (n : Nf α) → SCN n
all-scn K0        = λ x sx → K1 x ,
                               K0⇓ , (λ y sy → x , K1⇓ , sx , ≈K) , ≈refl
all-scn (K1 x)   = λ y sy → x , K1⇓ , all-scn x , ≈K
all-scn S0        = λ x sx → S1 x ,
                               S0⇓ ,
                                   (λ y sy → S2 x y ,
                                                 (S1⇓ ,
                                                     (λ z sz → 
  let pxz = sx z sz
      pyz = sy z sz
      pxzyz = (proj₁ ∘ proj₂) (proj₂ pxz) (proj₁ pyz) ((proj₁ ∘ proj₂) (proj₂ pyz)) 
  in proj₁ pxzyz ,
          (S2⇓ (proj₁ (proj₂ pxz)) (proj₁ (proj₂ pyz)) (proj₁ (proj₂ pxzyz)) ,
              (proj₁ ∘ proj₂) (proj₂ pxzyz) ,
              (≈trans ≈S 
                      (≈trans (≈cong∙ ((proj₂ ∘ proj₂) (proj₂ pxz)) ((proj₂ ∘ proj₂) (proj₂ pyz)))
                              ((proj₂ ∘ proj₂) (proj₂ pxzyz)))))) , ≈refl)) ,
  ≈refl
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
              (proj₁ ∘ proj₂) (proj₂ pxzyz) ,
              ≈trans ≈S 
                     (≈trans (≈cong∙ ((proj₂ ∘ proj₂) (proj₂ pxz)) ((proj₂ ∘ proj₂) (proj₂ pyz)))
                             ((proj₂ ∘ proj₂) (proj₂ pxzyz)))
all-scn Void0      = record {} 
all-scn Pr0        = λ x sx → 
  Pr1 x ,
      Pr0⇓ ,
          (λ y sy → Pr2 x y ,
                        Pr1⇓ ,
                            ((x , Fst0⇓ , sx , ≈Fst) ,
                                (y , Snd0⇓ , sy , ≈Snd)) ,
                            ≈refl) ,
          ≈refl
all-scn (Pr1 x)   = λ y sy → 
  Pr2 x y ,
      Pr1⇓ ,
          ((x , Fst0⇓ , all-scn x , ≈Fst) ,
              (y , Snd0⇓ , sy , ≈Snd)) ,
          ≈refl
all-scn (Pr2 x y) =
  (x , Fst0⇓ , all-scn x , ≈Fst) , (y , Snd0⇓ , all-scn y , ≈Snd)
all-scn Fst0      = λ _ → proj₁
all-scn Snd0      = λ _ → proj₂
all-scn NE0 = λ z sz → ZE sz 
all-scn (Inl1 x)  = all-scn x 
all-scn (Inr1 x)  = all-scn x 
all-scn Inl0 = λ x sx → Inl1 x , Inl0⇓ , sx , ≈refl
all-scn Inr0 = λ x sx → Inr1 x , Inr0⇓ , sx , ≈refl

all-scn C0        = λ l sl → 
  C1 l ,
      C0⇓ ,
          (λ r sr → C2 l r , C1⇓ , (λ c sc → all-scn-C3 l r c sl sr sc) , ≈refl) ,
          ≈refl
all-scn (C1 l)   = λ r sr → 
  C2 l r , C1⇓ , (λ c sc → all-scn-C3 l r c (all-scn l) sr sc) , ≈refl
all-scn (C2 l r) = λ c sc → all-scn-C3 l r c (all-scn l) (all-scn r) sc 
all-scn zeroⁿ = record {} 
all-scn sucⁿ = λ n _ → sucⁿ¹ n , rsucⁿ , record {} , ≈refl
all-scn (sucⁿ¹ n) = record {} 
all-scn Rⁿ = λ z sz → 
  Rⁿ¹ z , 
      (rRⁿ ,
          (λ f sf → Rⁿ² z f ,
                          rRⁿ¹ ,
                              (λ n _ → SCR z f n sz sf) ,
                              ≈refl) ,
          ≈refl)  
all-scn (Rⁿ¹ z) = λ f sf → 
  Rⁿ² z f ,
      rRⁿ¹ ,
          (λ n _ → SCR z f n (all-scn z) sf) ,
          ≈refl
all-scn (Rⁿ² z f) = λ n _ → SCR z f n (all-scn z) (all-scn f) 

SC : ∀ {α} → Tm α → Set
SC {α} t = Σ (Nf α) λ n → (t ⇓ n) × SCN n × (t ≈ ⌜ n ⌝)

all-sc : ∀ {α} → (t : Tm α) → SC t
all-sc K       = K0 , K⇓ , all-scn K0 , ≈refl
all-sc S       = S0 , S⇓ , all-scn S0 , ≈refl
all-sc (t ∙ u) with all-sc t          | all-sc u
all-sc (t ∙ u) | f , rf , sf , cf | a , ra , sa , ca with sf a sa
all-sc (t ∙ u) | f , rf , sf , cf | a , ra , sa , ca | v , rv , sv , cv
  = v , A⇓ rf ra rv , sv , ≈trans (≈cong∙ cf ca) cv
all-sc Void    = Void0 , Void⇓ , record {} , ≈refl
all-sc Pr      = 
  Pr0 ,
      Pr⇓ ,
          (λ x sx → Pr1 x ,
                        Pr0⇓ ,
                            (λ y sy → Pr2 x y ,
                                          Pr1⇓ ,
                                              ((x , Fst0⇓ , sx , ≈Fst) ,
                                                (y , Snd0⇓ , sy , ≈Snd)) ,
                                              ≈refl) ,
                            ≈refl) ,
          ≈refl
all-sc Fst     = Fst0 , Fst⇓ , (λ _ → proj₁) , ≈refl
all-sc Snd     = Snd0 , Snd⇓ , (λ _ → proj₂) , ≈refl
all-sc NE      = NE0 , NE⇓ , (λ z sz → ZE sz) , ≈refl
all-sc Inl = Inl0 , Inl⇓ , (λ x sx → Inl1 x , Inl0⇓ , sx , ≈refl) , ≈refl
all-sc Inr = Inr0 , Inr⇓ , (λ x sx → Inr1 x , Inr0⇓ , sx , ≈refl) , ≈refl
all-sc C       = 
  C0 ,
      C⇓ ,
          (λ l sl → C1 l ,
                        (C0⇓ ,
                            (λ r sr → C2 l r ,
                                          (C1⇓ ,
                                              (λ c sc → all-scn-C3 l r c sl sr sc) ,
                                              ≈refl)) ,
                            ≈refl)) ,
         ≈refl
all-sc zero    = zeroⁿ , rzero , record {} , ≈refl
all-sc suc     = 
  sucⁿ ,
      rsuc ,
          (λ n sn → sucⁿ¹ n ,
                        rsucⁿ , record {} , ≈refl) ,
          ≈refl
all-sc R       = 
  Rⁿ ,
      rR ,  
          (λ z sz → Rⁿ¹ z ,
                        rRⁿ ,
                            (λ f sf → Rⁿ² z f ,
                                          (rRⁿ¹ ,
                                              (λ n _ → SCR z f n sz sf) ,
                                              ≈refl)) ,
                            ≈refl) ,
          ≈refl
