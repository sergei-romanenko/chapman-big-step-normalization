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
  (Σ (Nf α) λ n → (fstⁿ ⟨∙⟩ p ⇓ n) × SCN n × (fst ∙ ⌜ p ⌝ ≈ ⌜ n ⌝))
  ×
  (Σ (Nf β) λ n → (sndⁿ ⟨∙⟩ p ⇓ n) × SCN n × (snd ∙ ⌜ p ⌝ ≈ ⌜ n ⌝))
SCN {α + β} (inlⁿ¹ x) = SCN x
SCN {α + β} (inrⁿ¹ x) = SCN x


SCC : ∀ {α β γ}(l : Nf (α ⇒ γ))(r : Nf (β ⇒ γ))(c : Nf (α + β)) →
      SCN l → SCN r → SCN c → 
      Σ (Nf γ) 
         λ n → (Cⁿ² l r ⟨∙⟩ c ⇓ n) × SCN n × (C ∙ ⌜ l ⌝ ∙ ⌜ r ⌝ ∙ ⌜ c ⌝ ≈ ⌜ n ⌝)
SCC l r (inlⁿ¹ x) sl sr sx = 
  proj₁ lx
    , rCⁿ²ˡ (proj₁ (proj₂ lx)) , (proj₁ ∘ proj₂) (proj₂ lx) , ≈trans Cl ((proj₂ ∘ proj₂) (proj₂ lx))
  where lx = sl x sx
SCC l r (inrⁿ¹ x) sl sr sx = 
  proj₁ rx
    , rCⁿ²ʳ (proj₁ (proj₂ rx)) , (proj₁ ∘ proj₂) (proj₂ rx) , ≈trans Cr ((proj₂ ∘ proj₂) (proj₂ rx))
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

prop1 : ∀ {α} → (n : Nf α) → SCN n
prop1 K0        = λ x sx → K1 x ,
                               K0⇓ , (λ y sy → x , K1⇓ , sx , ≈K) , ≈refl
prop1 (K1 x)   = λ y sy → x , K1⇓ , prop1 x , ≈K
prop1 S0        = λ x sx → S1 x ,
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
              (proj₁ ∘ proj₂) (proj₂ pxzyz) ,
              ≈trans ≈S 
                     (≈trans (≈cong∙ ((proj₂ ∘ proj₂) (proj₂ pxz)) ((proj₂ ∘ proj₂) (proj₂ pyz)))
                             ((proj₂ ∘ proj₂) (proj₂ pxzyz)))
prop1 voidⁿ      = record {} 
prop1 prⁿ        = λ x sx → 
  prⁿ¹ x ,
      rprⁿ ,
          (λ y sy → prⁿ² x y ,
                        rprⁿ¹ ,
                            ((x , rfstⁿ , sx , ≈fst) ,
                                (y , rsndⁿ , sy , ≈snd)) ,
                            ≈refl) ,
          ≈refl
prop1 (prⁿ¹ x)   = λ y sy → 
  prⁿ² x y ,
      rprⁿ¹ ,
          ((x , rfstⁿ , prop1 x , ≈fst) ,
              (y , rsndⁿ , sy , ≈snd)) ,
          ≈refl
prop1 (prⁿ² x y) =
  (x , rfstⁿ , prop1 x , ≈fst) , (y , rsndⁿ , prop1 y , ≈snd)
prop1 fstⁿ      = λ _ → proj₁
prop1 sndⁿ      = λ _ → proj₂
prop1 NEⁿ = λ z sz → ZE sz 
prop1 (inlⁿ¹ x)  = prop1 x 
prop1 (inrⁿ¹ x)  = prop1 x 
prop1 inlⁿ = λ x sx → inlⁿ¹ x , rinl , sx , ≈refl
prop1 inrⁿ = λ x sx → inrⁿ¹ x , rinr , sx , ≈refl

prop1 Cⁿ        = λ l sl → 
  Cⁿ¹ l ,
      rCⁿ ,
          (λ r sr → Cⁿ² l r , rCⁿ¹ , (λ c sc → SCC l r c sl sr sc) , ≈refl) ,
          ≈refl
prop1 (Cⁿ¹ l)   = λ r sr → 
  Cⁿ² l r , rCⁿ¹ , (λ c sc → SCC l r c (prop1 l) sr sc) , ≈refl
prop1 (Cⁿ² l r) = λ c sc → SCC l r c (prop1 l) (prop1 r) sc 
prop1 zeroⁿ = record {} 
prop1 sucⁿ = λ n _ → sucⁿ¹ n , rsucⁿ , record {} , ≈refl
prop1 (sucⁿ¹ n) = record {} 
prop1 Rⁿ = λ z sz → 
  Rⁿ¹ z , 
      (rRⁿ ,
          (λ f sf → Rⁿ² z f ,
                          rRⁿ¹ ,
                              (λ n _ → SCR z f n sz sf) ,
                              ≈refl) ,
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
prop2 void    = voidⁿ , rvoid , record {} , ≈refl
prop2 pr      = 
  prⁿ ,
      rpr ,
          (λ x sx → prⁿ¹ x ,
                        rprⁿ ,
                            (λ y sy → prⁿ² x y ,
                                          rprⁿ¹ ,
                                              ((x , rfstⁿ , sx , ≈fst) ,
                                                (y , rsndⁿ , sy , ≈snd)) ,
                                              ≈refl) ,
                            ≈refl) ,
          ≈refl
prop2 fst     = fstⁿ , rfst , (λ _ → proj₁) , ≈refl
prop2 snd     = sndⁿ , rsnd , (λ _ → proj₂) , ≈refl
prop2 NE      = NEⁿ , rNE , (λ z sz → ZE sz) , ≈refl
prop2 inl = inlⁿ , rinl , (λ x sx → inlⁿ¹ x , rinl , sx , ≈refl) , ≈refl
prop2 inr = inrⁿ , rinr , (λ x sx → inrⁿ¹ x , rinr , sx , ≈refl) , ≈refl
prop2 C       = 
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
                                          (rRⁿ¹ ,
                                              (λ n _ → SCR z f n sz sf) ,
                                              ≈refl)) ,
                            ≈refl) ,
          ≈refl
