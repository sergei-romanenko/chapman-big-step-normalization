module FiniteProducts.Soundness where

open import FiniteProducts.Utils
open import FiniteProducts.Syntax
open import FiniteProducts.Conversion
open import FiniteProducts.OPE
open import FiniteProducts.OPELemmas
open import FiniteProducts.BigStepSemantics
open import FiniteProducts.OPEBigStep
open import FiniteProducts.StrongComputability
open import FiniteProducts.StructuralNormaliser 
open import FiniteProducts.StrongConvertibility

--
-- Soundness: t₁ ≈ t₂ → nf t₁ ≡ nf t₂
-- (Normalisation takes convertible terms to identical normal forms.)
--

--
-- ρ₁ ~~ ρ₂ →
--     ∃₂ λ u₁ u₂ → u₁ ~ u₂ × ⟦ t ⟧ ρ₁ ⇓ u₁ × ⟦ t ⟧ ρ₂ ⇓ u₂
-- ρ₁ ~~ ρ₂ →
--     ∃₂ λ θ₁ θ₂ → θ₁ ~~ θ₂ × (⟦ σ ⟧* ρ₁ ⇓ θ₁) × (⟦ σ ⟧* ρ₂ ⇓ θ₂)

mutual

  ~cong⟦≡⟧ : ∀ {α Γ Δ} (t : Tm Δ α) {ρ₁ ρ₂ : Env Γ Δ}
    (ρ₁~~ρ₂ : ρ₁ ~~ ρ₂) →
    ∃₂ λ u₁ u₂ → u₁ ~ u₂ × ⟦ t ⟧ ρ₁ ⇓ u₁ × ⟦ t ⟧ ρ₂ ⇓ u₂

  ~cong⟦≡⟧ ø {u₁ ∷ ρ₁} {u₂ ∷ ρ₂} (u₁~u₂ ∷ ρ₁~~ρ₂) =
    u₁ , u₂ , u₁~u₂ , ø⇓ , ø⇓
  ~cong⟦≡⟧ (t ∙ t′) ρ₁~~ρ₂
    with ~cong⟦≡⟧ t ρ₁~~ρ₂ | ~cong⟦≡⟧ t′ ρ₁~~ρ₂
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂ | v₁ , v₂ , v₁~v₂ , ⇓v₁ , ⇓v₂
    with u₁~u₂ ≤id v₁~v₂
  ... | w₁ , w₂ , w₁~w₂ , ⇓w₁ , ⇓w₂
    rewrite val≤ ≤id u₁ ≡ u₁ ∋ val≤-≤id u₁ |
            val≤ ≤id u₂ ≡ u₂ ∋ val≤-≤id u₂
    = w₁ , w₂ , w₁~w₂ , ∙⇓ ⇓u₁ ⇓v₁ ⇓w₁ , ∙⇓ ⇓u₂ ⇓v₂ ⇓w₂
  ~cong⟦≡⟧ {α ⇒ β} {Γ} (ƛ t) {ρ₁} {ρ₂} ρ₁~~ρ₂ =
    lam t ρ₁ , lam t ρ₂ , h , ƛ⇓ , ƛ⇓
    where
    h : ∀ {Β} (η : Β ≤ Γ) {u₁ u₂ : Val Β α} → u₁ ~ u₂ →
          ∃₂ (λ w₁ w₂ → w₁ ~ w₂
            × lam t (env≤ η ρ₁) ⟨∙⟩ u₁ ⇓ w₁
            × lam t (env≤ η ρ₂) ⟨∙⟩ u₂ ⇓ w₂)
    h {Β} η u₁~u₂
      with ~cong⟦≡⟧ t (u₁~u₂ ∷ ~~≤ η ρ₁~~ρ₂)
    ... | v₁ , v₂ , v₁~v₂ , ⇓v₁ , ⇓v₂
      = v₁ , v₂ , v₁~v₂ , lam⇓ ⇓v₁ , lam⇓ ⇓v₂
  ~cong⟦≡⟧ (t [ σ ]) ρ₁~~ρ₂
    with ~~cong⟦≡⟧* σ ρ₁~~ρ₂
  ... | θ₁ , θ₂ , θ₁~~θ₂ , ⇓θ₁ , ⇓θ₂
    with ~cong⟦≡⟧ t θ₁~~θ₂
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂
    = u₁ , u₂ , u₁~u₂ , []⇓ ⇓θ₁ ⇓u₁ , []⇓ ⇓θ₂ ⇓u₂
  ~cong⟦≡⟧ void ρ₁~~ρ₂ =
    void , void , tt , void⇓ , void⇓
  ~cong⟦≡⟧ (pair tu tv) ρ₁~~ρ₂
    with ~cong⟦≡⟧ tu ρ₁~~ρ₂ | ~cong⟦≡⟧ tv ρ₁~~ρ₂
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂ | v₁ , v₂ , v₁~v₂ , ⇓v₁ , ⇓v₂
    = pair u₁ v₁ , pair u₂ v₂ ,
           ((u₁ , u₂ , fst-pair⇓ , fst-pair⇓ , u₁~u₂) ,
             (v₁ , v₂ , snd-pair⇓ , snd-pair⇓ , v₁~v₂)) ,
             pair⇓ ⇓u₁ ⇓v₁ , pair⇓ ⇓u₂ ⇓v₂
  ~cong⟦≡⟧ (fst t) ρ₁~~ρ₂
    with ~cong⟦≡⟧ t ρ₁~~ρ₂
  ... | u₁ , u₂ ,
    ((f₁ , f₂ , ⇓f₁ , ⇓f₂ , f₁~f₂) , (s₁ , s₂ , ⇓s₁ , ⇓s₂ , s₁~s₂)) ,
      ⇓u₁ , ⇓u₂
    = f₁ , f₂ , f₁~f₂ , fst⇓ ⇓u₁ ⇓f₁ , fst⇓ ⇓u₂ ⇓f₂
  ~cong⟦≡⟧ (snd t) ρ₁~~ρ₂
    with ~cong⟦≡⟧ t ρ₁~~ρ₂
  ... | u₁ , u₂ ,
    ((f₁ , f₂ , ⇓f₁ , ⇓f₂ , f₁~f₂) , (s₁ , s₂ , ⇓s₁ , ⇓s₂ , s₁~s₂)) ,
      ⇓u₁ , ⇓u₂
    = s₁ , s₂ , s₁~s₂ , snd⇓ ⇓u₁ ⇓s₁ , snd⇓ ⇓u₂ ⇓s₂

  ~~cong⟦≡⟧* : ∀ {Γ Δ Δ′} (σ : Sub Δ Δ′)
    {ρ₁ ρ₂ : Env Γ Δ} (ρ₁~~ρ₂ : ρ₁ ~~ ρ₂) →
    ∃₂ λ θ₁ θ₂ → θ₁ ~~ θ₂ × (⟦ σ ⟧* ρ₁ ⇓ θ₁) × (⟦ σ ⟧* ρ₂ ⇓ θ₂)

  ~~cong⟦≡⟧* ı {ρ₁} {ρ₂} ρ₁~~ρ₂ =
    ρ₁ , ρ₂ , ρ₁~~ρ₂ , ι⇓ , ι⇓
  ~~cong⟦≡⟧* (σ ○ σ′) ρ₁~~ρ₂
    with ~~cong⟦≡⟧* σ′ ρ₁~~ρ₂
  ... | θ₁ , θ₂ , θ₁~θ₂ , ⇓θ₁ , ⇓θ₂
    with ~~cong⟦≡⟧* σ θ₁~θ₂
  ... | φ₁ , φ₂ , φ₁~φ₂ , ⇓φ₁ , ⇓φ₂
    = φ₁ , φ₂ , φ₁~φ₂ , ○⇓ ⇓θ₁ ⇓φ₁ , ○⇓ ⇓θ₂ ⇓φ₂
  ~~cong⟦≡⟧* (t ∷ σ) ρ₁~~ρ₂
    with ~cong⟦≡⟧ t ρ₁~~ρ₂ | ~~cong⟦≡⟧* σ ρ₁~~ρ₂
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂ | θ₁ , θ₂ , θ₁~~θ₂ , ⇓θ₁ , ⇓θ₂
    = u₁ ∷ θ₁ , u₂ ∷ θ₂ , u₁~u₂ ∷ θ₁~~θ₂ , ∷⇓ ⇓u₁ ⇓θ₁ , ∷⇓ ⇓u₂ ⇓θ₂
  ~~cong⟦≡⟧* ↑ {u₁ ∷ ρ₁} {u₂ ∷ ρ₂} (u₁~u₂ ∷ ρ₁~~ρ₂) =
    ρ₁ , ρ₂ , ρ₁~~ρ₂ , ↑⇓ , ↑⇓

--
-- t₁ ≈ t₂ → ρ₁ ~~ ρ₂ →
--     ∃₂ λ u₁ u₂ → u₁ ~ u₂ × ⟦ t₁ ⟧ ρ₁ ⇓ u₁ × ⟦ t₂ ⟧ ρ₂ ⇓ u₂
--
-- σ₁ ≈≈ σ₂ → ρ₁ ~~ ρ₂ →
--     ∃₂ λ θ₁ θ₂ → θ₁ ~~ θ₂ × ⟦ σ₁ ⟧* ρ₁ ⇓ θ₁ × ⟦ σ₂ ⟧* ρ₂ ⇓ θ₂
--

mutual

  ~cong⟦⟧ : ∀ {α Γ Δ}
    {t₁ t₂ : Tm Δ α} (t₁≈t₂ : t₁ ≈ t₂)
    {ρ₁ ρ₂ : Env Γ Δ} (ρ₁~~ρ₂ : ρ₁ ~~ ρ₂) →
    ∃₂ λ u₁ u₂ → u₁ ~ u₂ × ⟦ t₁ ⟧ ρ₁ ⇓ u₁ × ⟦ t₂ ⟧ ρ₂ ⇓ u₂

  ~cong⟦⟧ {t₁ = t} ≈refl ρ₁~~ρ₂ =
    ~cong⟦≡⟧ t ρ₁~~ρ₂
  ~cong⟦⟧ {α} (≈sym t₁≈t₂) ρ₁~~ρ₂
    with ~cong⟦⟧ t₁≈t₂ (~~sym ρ₁~~ρ₂)
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂
    = u₂ , u₁ , ~sym {α} u₁~u₂ , ⇓u₂ , ⇓u₁
  ~cong⟦⟧ {α} (≈trans t₁≈t₂ t₂≈t₃) ρ₁~~ρ₂
    with ~cong⟦⟧ t₁≈t₂ (~~refl′ ρ₁~~ρ₂) | ~cong⟦⟧ t₂≈t₃ ρ₁~~ρ₂
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂ | v₁ , v₂ , v₁~v₂ , ⇓v₁ , ⇓v₂
    rewrite u₂ ≡ v₁ ∋ ⟦⟧⇓-det ⇓u₂ ⇓v₁ refl
    = u₁ , v₂ , ~trans {α} u₁~u₂ v₁~v₂ , ⇓u₁ , ⇓v₂
  ~cong⟦⟧ {t₁ = f₁ ∙ t₁} {t₂ = f₂ ∙ t₂} (≈cong∙ f₁≈f₂ t₁≈t₂) ρ₁~~ρ₂
    with ~cong⟦⟧ f₁≈f₂ ρ₁~~ρ₂
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂
    with ~cong⟦⟧ t₁≈t₂ ρ₁~~ρ₂
  ... | v₁ , v₂ , v₁~v₂ , ⇓v₁ , ⇓v₂
    with u₁~u₂ ≤id v₁~v₂
  ... | w₁ , w₂ , w₁~w₂ , ⇓w₁ , ⇓w₂
    rewrite val≤ ≤id u₁ ≡ u₁ ∋ val≤-≤id u₁ |
            val≤ ≤id u₂ ≡ u₂ ∋ val≤-≤id u₂
    = w₁ , w₂ , w₁~w₂ , ∙⇓ ⇓u₁ ⇓v₁ ⇓w₁ , ∙⇓ ⇓u₂ ⇓v₂ ⇓w₂
  ~cong⟦⟧ (≈cong[] t₁≈t₂ σ₁≈≈σ₂) ρ₁~~ρ₂
    with ~~cong⟦⟧* σ₁≈≈σ₂ ρ₁~~ρ₂
  ... | θ₁ , θ₂ , θ₁~θ₂ , ⇓θ₁ , ⇓θ₂
    with ~cong⟦⟧ t₁≈t₂ θ₁~θ₂
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂
    = u₁ , u₂ , u₁~u₂ , []⇓ ⇓θ₁ ⇓u₁ , []⇓ ⇓θ₂ ⇓u₂
  ~cong⟦⟧ {t₁ = (ƛ t₁)} {t₂ = (ƛ t₂)} (≈congƛ t₁≈t₂) {ρ₁} {ρ₂} ρ₁~~ρ₂
    = lam t₁ ρ₁ , lam t₂ ρ₂ , h , ƛ⇓ , ƛ⇓
    where
    h : lam t₁ ρ₁ ~ lam t₂ ρ₂
    h {Β} η {u₁} {u₂} u₁~u₂
      with ~cong⟦⟧ t₁≈t₂ (u₁~u₂ ∷ ~~≤ η ρ₁~~ρ₂)
    ... | v₁ , v₂ , v₁~v₂ , ⇓v₁ , ⇓v₂
      = v₁ , v₂ , v₁~v₂ , lam⇓ ⇓v₁ , lam⇓ ⇓v₂
  ~cong⟦⟧ {t₁ = ø [ t ∷ σ ]} ≈proj ρ₁~~ρ₂
    with ~cong⟦≡⟧ t ρ₁~~ρ₂ | ~~cong⟦≡⟧* σ ρ₁~~ρ₂
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂ | θ₁ , θ₂ , θ₁~θ₂ , ⇓θ₁ , ⇓θ₂
    = u₁ , u₂ , u₁~u₂ , []⇓ (∷⇓ ⇓u₁ ⇓θ₁) ø⇓ , ⇓u₂
  ~cong⟦⟧ {t₁ = t [ ı ]} ≈id ρ₁~~ρ₂
    with ~cong⟦≡⟧ t ρ₁~~ρ₂
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂
    = u₁ , u₂ , u₁~u₂ , []⇓ ι⇓ ⇓u₁ , ⇓u₂
  ~cong⟦⟧ {t₁ = t [ σ ○ σ′ ]} ≈comp ρ₁~~ρ₂
    with ~~cong⟦≡⟧* σ′ ρ₁~~ρ₂
  ... | θ₁ , θ₂ , θ₁~θ₂ , ⇓θ₁ , ⇓θ₂
    with ~~cong⟦≡⟧* σ θ₁~θ₂
  ... | φ₁ , φ₂ , φ₁~φ₂ , ⇓φ₁ , ⇓φ₂
    with ~cong⟦≡⟧ t φ₁~φ₂
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂
    = u₁ , u₂ , u₁~u₂ ,
         []⇓ (○⇓ ⇓θ₁ ⇓φ₁) ⇓u₁ , []⇓ ⇓θ₂ ([]⇓ ⇓φ₂ ⇓u₂)
  ~cong⟦⟧ {α ⇒ β} {Γ} {t₁ = (ƛ t) [ σ ]} ≈lam {ρ₁} {ρ₂} ρ₁~~ρ₂
    with ~~cong⟦≡⟧* σ ρ₁~~ρ₂
  ... | θ₁ , θ₂ , θ₁~θ₂ , ⇓θ₁ , ⇓θ₂
    with ~cong⟦≡⟧ (ƛ t) θ₁~θ₂
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂
    = u₁ , lam (t [ ø ∷ (σ ○ ↑) ]) ρ₂ , h , []⇓ ⇓θ₁ ⇓u₁ , ƛ⇓
    where
    h : ∀ {Β} (η : Β ≤ Γ) {v₁ v₂ : Val Β α} (v₁~v₂ : v₁ ~ v₂) →
          ∃₂ λ w₁ w₃ → w₁ ~ w₃
               × val≤ η u₁ ⟨∙⟩ v₁ ⇓ w₁
               × lam (t [ ø ∷ (σ ○ ↑) ]) (env≤ η ρ₂) ⟨∙⟩ v₂ ⇓ w₃
    h {Β} η {v₁} {v₂} v₁~v₂
      with ~cong⟦≡⟧ t (v₁~v₂ ∷ ~~≤ η θ₁~θ₂)
    ... | y₁ , y₂ , y₁~y₂ , ⇓y₁ , ⇓y₂
      rewrite val≤ η u₁ ≡ lam t (env≤ η θ₁)
                   ∋ ⟦⟧⇓-det (⟦⟧⇓≤ η ⇓u₁) ƛ⇓ refl
      = y₁ , y₂ , y₁~y₂ , lam⇓ ⇓y₁ ,
           lam⇓ ([]⇓ (∷⇓ ø⇓ (○⇓ ↑⇓ (⟦⟧*⇓≤ η ⇓θ₂))) ⇓y₂)
  ~cong⟦⟧ {t₁ = (t ∙ t′) [ σ ]} ≈app {ρ₁} {ρ₂} ρ₁~~ρ₂
    with ~~cong⟦≡⟧* σ ρ₁~~ρ₂
  ... | θ₁ , θ₂ , θ₁~θ₂ , ⇓θ₁ , ⇓θ₂
    with ~cong⟦≡⟧ t θ₁~θ₂ | ~cong⟦≡⟧ t′ θ₁~θ₂
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂ | v₁ , v₂ , v₁~v₂ , ⇓v₁ , ⇓v₂
    with u₁~u₂ ≤id v₁~v₂
  ... | w₁ , w₂ , w₁~w₂ , ⇓w₁ , ⇓w₂
    rewrite val≤ ≤id u₁ ≡ u₁ ∋ val≤-≤id u₁ |
            val≤ ≤id u₂ ≡ u₂ ∋ val≤-≤id u₂
    = w₁ , w₂ , w₁~w₂ ,
         []⇓ ⇓θ₁ (∙⇓ ⇓u₁ ⇓v₁ ⇓w₁) ,
           ∙⇓ ([]⇓ ⇓θ₂ ⇓u₂) ([]⇓ ⇓θ₂ ⇓v₂) ⇓w₂
  ~cong⟦⟧ {t₁ = (ƛ t) [ σ ] ∙ t′} ≈βσ {ρ₁} {ρ₂} ρ₁~~ρ₂
    with ~cong⟦≡⟧ t′ ρ₁~~ρ₂ | ~~cong⟦≡⟧* σ ρ₁~~ρ₂
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂ | θ₁ , θ₂ , θ₁~θ₂ , ⇓θ₁ , ⇓θ₂
    with ~cong⟦≡⟧ t (u₁~u₂ ∷ θ₁~θ₂)
  ... | v₁ , v₂ , v₁~v₂ , ⇓v₁ , ⇓v₂
    = v₁ , v₂ , v₁~v₂ ,
      ∙⇓ ([]⇓ ⇓θ₁ ƛ⇓) ⇓u₁ (lam⇓ ⇓v₁) , []⇓ (∷⇓ ⇓u₂ ⇓θ₂) ⇓v₂
  ~cong⟦⟧ {α ⇒ β} {Γ} {Δ} {t₂ = ƛ (t [ ↑ ] ∙ ø)} ≈η {ρ₁} {ρ₂} ρ₁~~ρ₂
    with ~cong⟦≡⟧ t ρ₁~~ρ₂
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂
    = u₁ , lam (t [ ↑ ] ∙ ø) ρ₂ , h , ⇓u₁ , ƛ⇓
    where
    h : ∀ {Β} (η : Β ≤ Γ) {v₁ v₂ : Val Β α} (v₁~v₂ : v₁ ~ v₂) →
          ∃₂ λ w₁ w₃ → w₁ ~ w₃
               × val≤ η u₁ ⟨∙⟩ v₁ ⇓ w₁
               × val≤ η (lam (t [ ↑ ] ∙ ø) ρ₂) ⟨∙⟩ v₂ ⇓ w₃
    h {Β} η {v₁} {v₂} v₁~v₂
      with ~≤ η {u₁} u₁~u₂ {Β} ≤id v₁~v₂
    ... | w₁ , w₂ , w₁~w₂ , ⇓w₁ , ⇓w₂
      rewrite val≤ ≤id (val≤ η u₁) ≡ val≤ η u₁ ∋ val≤-≤id (val≤ η u₁) |
              val≤ ≤id (val≤ η u₂) ≡ val≤ η u₂ ∋ val≤-≤id (val≤ η u₂)
      = w₁ , w₂ , w₁~w₂ , ⇓w₁ , g
      where
      g : lam (t [ ↑ ] ∙ ø) (env≤ η ρ₂) ⟨∙⟩ v₂ ⇓ w₂
      g = lam⇓ (∙⇓ ([]⇓ ↑⇓ (⟦⟧⇓≤ η ⇓u₂)) ø⇓ ⇓w₂)
  ~cong⟦⟧ {t₁ = pair f₁ s₁} {t₂ = pair f₂ s₂} (≈cong-pair f₁≈f₂ s₁≈s₂) ρ₁~~ρ₂
    with ~cong⟦⟧ f₁≈f₂ ρ₁~~ρ₂ | ~cong⟦⟧ s₁≈s₂ ρ₁~~ρ₂
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂ | v₁ , v₂ , v₁~v₂ , ⇓v₁ , ⇓v₂
    = pair u₁ v₁ , pair u₂ v₂ ,
           ((u₁ , u₂ , fst-pair⇓ , fst-pair⇓ , u₁~u₂) ,
             (v₁ , v₂ , snd-pair⇓ , snd-pair⇓ , v₁~v₂)) ,
           pair⇓ ⇓u₁ ⇓v₁ , pair⇓ ⇓u₂ ⇓v₂
  ~cong⟦⟧ {t₁ = fst t₁} {t₂ = fst t₂} (≈cong-fst t₁≈t₂) ρ₁~~ρ₂
    with ~cong⟦⟧ t₁≈t₂ ρ₁~~ρ₂
  ... | u₁ , u₂ , ((f₁ , f₂ , ⇓f₁ , ⇓f₂ , f₁~f₂) , _) , ⇓u₁ , ⇓u₂
    = f₁ , f₂ , f₁~f₂ , fst⇓ ⇓u₁ ⇓f₁ , fst⇓ ⇓u₂ ⇓f₂
  ~cong⟦⟧ (≈cong-snd t₁≈t₂) ρ₁~~ρ₂
    with ~cong⟦⟧ t₁≈t₂ ρ₁~~ρ₂
  ... | u₁ , u₂ , (_ , (s₁ , s₂ , ⇓s₁ , ⇓s₂ , s₁~s₂)) , ⇓u₁ , ⇓u₂
    = s₁ , s₂ , s₁~s₂ , snd⇓ ⇓u₁ ⇓s₁ , snd⇓ ⇓u₂ ⇓s₂
  ~cong⟦⟧ {t₁ = void [ σ ]} ≈void[] ρ₁~~ρ₂
    with ~~cong⟦≡⟧* σ ρ₁~~ρ₂
  ... | θ₁ , θ₂ , θ₁~θ₂ , ⇓θ₁ , ⇓θ₂
    = void , void , tt , []⇓ ⇓θ₁ void⇓ , void⇓
  ~cong⟦⟧ {t₁ = pair f s [ σ ]} ≈pair[] ρ₁~~ρ₂
    with ~~cong⟦≡⟧* σ ρ₁~~ρ₂
  ... | θ₁ , θ₂ , θ₁~θ₂ , ⇓θ₁ , ⇓θ₂
    with ~cong⟦≡⟧ f θ₁~θ₂ | ~cong⟦≡⟧ s θ₁~θ₂
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂ | v₁ , v₂ , v₁~v₂ , ⇓v₁ , ⇓v₂
    = pair u₁ v₁ , pair u₂ v₂ ,
      ((u₁ , u₂ , fst-pair⇓ , fst-pair⇓ , u₁~u₂) ,
        (v₁ , v₂ , snd-pair⇓ , snd-pair⇓ , v₁~v₂)) ,
      []⇓ ⇓θ₁ (pair⇓ ⇓u₁ ⇓v₁) , pair⇓ ([]⇓ ⇓θ₂ ⇓u₂) ([]⇓ ⇓θ₂ ⇓v₂)
  ~cong⟦⟧ {t₁ = fst t [ σ ]} ≈fst[] ρ₁~~ρ₂
    with ~~cong⟦≡⟧* σ ρ₁~~ρ₂
  ... | θ₁ , θ₂ , θ₁~θ₂ , ⇓θ₁ , ⇓θ₂
    with ~cong⟦≡⟧ t θ₁~θ₂
  ... | u₁ , u₂ ,
        ((x₁ , x₂ , ⇓x₁ , ⇓x₂ , x₁~x₂) , (y₁ , y₂ , ⇓y₁ , ⇓y₂ , y₁~y₂)) ,
        ⇓u₁ , ⇓u₂
    = x₁ , x₂ , x₁~x₂ ,
      []⇓ ⇓θ₁ (fst⇓ ⇓u₁ ⇓x₁) , fst⇓ ([]⇓ ⇓θ₂ ⇓u₂) ⇓x₂
  ~cong⟦⟧ {t₁ = snd t [ σ ]} ≈snd[] ρ₁~~ρ₂
    with ~~cong⟦≡⟧* σ ρ₁~~ρ₂
  ... | θ₁ , θ₂ , θ₁~θ₂ , ⇓θ₁ , ⇓θ₂
    with ~cong⟦≡⟧ t θ₁~θ₂
  ... | u₁ , u₂ ,
        ((x₁ , x₂ , ⇓x₁ , ⇓x₂ , x₁~x₂) , (y₁ , y₂ , ⇓y₁ , ⇓y₂ , y₁~y₂)) ,
        ⇓u₁ , ⇓u₂
    = y₁ , y₂ , y₁~y₂ ,
      []⇓ ⇓θ₁ (snd⇓ ⇓u₁ ⇓y₁) , snd⇓ ([]⇓ ⇓θ₂ ⇓u₂) ⇓y₂
  ~cong⟦⟧ {t₁ = fst (pair f s)} ≈βfst ρ₁~~ρ₂
    with ~cong⟦≡⟧ f ρ₁~~ρ₂ | ~cong⟦≡⟧ s ρ₁~~ρ₂
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂ | v₁ , v₂ , v₁~v₂ , ⇓v₁ , ⇓v₂
    = u₁ , u₂ , u₁~u₂ , fst⇓ (pair⇓ ⇓u₁ ⇓v₁) fst-pair⇓ , ⇓u₂
  ~cong⟦⟧ {t₁ = snd (pair f s)} ≈βsnd ρ₁~~ρ₂
    with ~cong⟦≡⟧ f ρ₁~~ρ₂ | ~cong⟦≡⟧ s ρ₁~~ρ₂
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂ | v₁ , v₂ , v₁~v₂ , ⇓v₁ , ⇓v₂
    = v₁ , v₂ , v₁~v₂ , snd⇓ (pair⇓ ⇓u₁ ⇓v₁) snd-pair⇓ , ⇓v₂
  ~cong⟦⟧ {t₁ = t} ≈ηpair ρ₁~~ρ₂
    with ~cong⟦≡⟧ t ρ₁~~ρ₂
  ... | u₁ , u₂ ,
        ((x₁ , x₂ , ⇓x₁ , ⇓x₂ , x₁~x₂) , (y₁ , y₂ , ⇓y₁ , ⇓y₂ , y₁~y₂)) ,
        ⇓u₁ , ⇓u₂
    = u₁ , pair x₂ y₂ ,
      ((x₁ , x₂ , ⇓x₁ , fst-pair⇓ , x₁~x₂) ,
           y₁ , y₂ , ⇓y₁ , snd-pair⇓ , y₁~y₂) ,
      ⇓u₁ , pair⇓ (fst⇓ ⇓u₂ ⇓x₂) (snd⇓ ⇓u₂ ⇓y₂)
  ~cong⟦⟧ {t₁ = t} ≈ηvoid ρ₁~~ρ₂
    with ~cong⟦≡⟧ t ρ₁~~ρ₂ | ~cong⟦≡⟧ void ρ₁~~ρ₂
  ... | u₁ , u₂ , tt , ⇓u₁ , ⇓u₂ | v₁ , v₂ , tt , ⇓v₁ , ⇓v₂
    = u₁ , void , tt , ⇓u₁ , void⇓

  ~~cong⟦⟧* : ∀ {Γ Δ Δ′}
    {σ₁ σ₂ : Sub Δ Δ′} (σ₁≈≈σ₂ : σ₁ ≈≈ σ₂)
    {ρ₁ ρ₂ : Env Γ Δ} (ρ₁~~ρ₂ : ρ₁ ~~ ρ₂) →
    ∃₂ λ θ₁ θ₂ → θ₁ ~~ θ₂ × ⟦ σ₁ ⟧* ρ₁ ⇓ θ₁ × ⟦ σ₂ ⟧* ρ₂ ⇓ θ₂

  ~~cong⟦⟧* {σ₁ = σ} ≈≈refl ρ₁~~ρ₂ =
    ~~cong⟦≡⟧* σ ρ₁~~ρ₂
  ~~cong⟦⟧* (≈≈sym σ₁≈≈σ₂) ρ₁~~ρ₂
    with ~~cong⟦⟧* σ₁≈≈σ₂ (~~sym ρ₁~~ρ₂)
  ... | θ₁ , θ₂ , θ₁~θ₂ , ⇓θ₁ , ⇓θ₂
    = θ₂ , θ₁ , ~~sym θ₁~θ₂ , ⇓θ₂ , ⇓θ₁
  ~~cong⟦⟧* (≈≈trans σ₁≈≈σ₂ σ₂≈≈σ₃) ρ₁~~ρ₂
    with ~~cong⟦⟧* σ₁≈≈σ₂ (~~refl′ ρ₁~~ρ₂) | ~~cong⟦⟧* σ₂≈≈σ₃ ρ₁~~ρ₂
  ... | θ₁ , θ₂ , θ₁~θ₂ , ⇓θ₁ , ⇓θ₂ | φ₁ , φ₂ , φ₁~φ₂ , ⇓φ₁ , ⇓φ₂
    rewrite θ₂ ≡ φ₁ ∋ ⟦⟧*⇓-det ⇓θ₂ ⇓φ₁ refl
    = θ₁ , φ₂ , ~~trans θ₁~θ₂ φ₁~φ₂ , ⇓θ₁ , ⇓φ₂
  ~~cong⟦⟧* (≈≈cong○ σ₁≈≈σ₂ τ₁≈≈τ₂) ρ₁~~ρ₂
    with ~~cong⟦⟧* τ₁≈≈τ₂ ρ₁~~ρ₂
  ... | θ₁ , θ₂ , θ₁~θ₂ , ⇓θ₁ , ⇓θ₂
    with ~~cong⟦⟧* σ₁≈≈σ₂ θ₁~θ₂
  ... | φ₁ , φ₂ , φ₁~φ₂ , ⇓φ₁ , ⇓φ₂
    = φ₁ , φ₂ , φ₁~φ₂ , ○⇓ ⇓θ₁ ⇓φ₁ , ○⇓ ⇓θ₂ ⇓φ₂
  ~~cong⟦⟧* (≈≈cong∷ t₁≈t₂ σ₁≈≈σ₂) ρ₁~~ρ₂
    with ~cong⟦⟧ t₁≈t₂ ρ₁~~ρ₂ | ~~cong⟦⟧* σ₁≈≈σ₂ ρ₁~~ρ₂
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂ | θ₁ , θ₂ , θ₁~θ₂ , ⇓θ₁ , ⇓θ₂
    = u₁ ∷ θ₁ , u₂ ∷ θ₂ , u₁~u₂ ∷ θ₁~θ₂ , ∷⇓ ⇓u₁ ⇓θ₁ , ∷⇓ ⇓u₂ ⇓θ₂
  ~~cong⟦⟧* {σ₁ = (σ₁ ○ σ₂) ○ σ₃} ≈≈assoc ρ₁~~ρ₂
    with ~~cong⟦≡⟧* σ₃ ρ₁~~ρ₂
  ... | θ₁ , θ₂ , θ₁~θ₂ , ⇓θ₁ , ⇓θ₂
    with ~~cong⟦≡⟧* σ₂ θ₁~θ₂
  ... | φ₁ , φ₂ , φ₁~φ₂ , ⇓φ₁ , ⇓φ₂
    with ~~cong⟦≡⟧* σ₁ φ₁~φ₂
  ... | ψ₁ , ψ₂ , ψ₁~ψ₂ , ⇓ψ₁ , ⇓ψ₂
    = ψ₁ , ψ₂ , ψ₁~ψ₂ , ○⇓ ⇓θ₁ (○⇓ ⇓φ₁ ⇓ψ₁) , ○⇓ (○⇓ ⇓θ₂ ⇓φ₂) ⇓ψ₂
  ~~cong⟦⟧* {σ₂ = σ} ≈≈idl ρ₁~~ρ₂
    with ~~cong⟦≡⟧* σ ρ₁~~ρ₂
  ... | θ₁ , θ₂ , θ₁~θ₂ , ⇓θ₁ , ⇓θ₂
    = θ₁ , θ₂ , θ₁~θ₂ , ○⇓ ⇓θ₁ ι⇓ , ⇓θ₂
  ~~cong⟦⟧* {σ₂ = σ} ≈≈idr ρ₁~~ρ₂
    with ~~cong⟦≡⟧* σ ρ₁~~ρ₂
  ... | θ₁ , θ₂ , θ₁~θ₂ , ⇓θ₁ , ⇓θ₂
    = θ₁ , θ₂ , θ₁~θ₂ , ○⇓ ι⇓ ⇓θ₁ , ⇓θ₂
  ~~cong⟦⟧* {σ₁ = ↑ ○ (t ∷ σ)} ≈≈wk {ρ₁} {ρ₂} ρ₁~~ρ₂
    with ~cong⟦≡⟧ t ρ₁~~ρ₂ | ~~cong⟦≡⟧* σ ρ₁~~ρ₂
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂ | θ₁ , θ₂ , θ₁~θ₂ , ⇓θ₁ , ⇓θ₂
    = θ₁ , θ₂ , θ₁~θ₂ , ○⇓ (∷⇓ ⇓u₁ ⇓θ₁) ↑⇓ , ⇓θ₂
  ~~cong⟦⟧*  {σ₁ = (t ∷ σ) ○ σ′} ≈≈cons ρ₁~~ρ₂
    with ~~cong⟦≡⟧* σ′ ρ₁~~ρ₂
  ... | θ₁ , θ₂ , θ₁~θ₂ , ⇓θ₁ , ⇓θ₂
    with ~cong⟦≡⟧ t θ₁~θ₂ | ~~cong⟦≡⟧* σ θ₁~θ₂
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂ | φ₁ , φ₂ , φ₁~φ₂ , ⇓φ₁ , ⇓φ₂
    = u₁ ∷ φ₁ , u₂ ∷ φ₂ , u₁~u₂ ∷ φ₁~φ₂ ,
         ○⇓ ⇓θ₁ (∷⇓ ⇓u₁ ⇓φ₁) , ∷⇓ ([]⇓ ⇓θ₂ ⇓u₂) (○⇓ ⇓θ₂ ⇓φ₂)
  ~~cong⟦⟧* ≈≈id∷ (_∷_ {u₁ = u₁} {u₂} {ρ₁} {ρ₂} u₁~u₂ ρ₁~~ρ₂)
    = u₁ ∷ ρ₁ , u₂ ∷ ρ₂ , u₁~u₂ ∷ ρ₁~~ρ₂ , ι⇓ , ∷⇓ ø⇓ (○⇓ ↑⇓ ι⇓)


--
-- Soundness: t₁ ≈ t₂ → nf t₁ ≡ nf t₂
--

sound : ∀ {α Γ} {t₁ t₂ : Tm Γ α} →
  t₁ ≈ t₂ → nf t₁ ≡ nf t₂

sound {α} {Γ} {t₁} {t₂} t₁≈t₂
  with all-scv t₁ id-env sce-id-env | all-scv t₂ id-env sce-id-env
... | u₁ , p₁ , ⇓u₁ , ≈u₁ | u₂ , p₂ , ⇓u₂ , ≈u₂
  with all-quote u₁ p₁ | all-quote u₂ p₂
... | m₁ , ⇓m₁ , ≈m₁ | m₂ , ⇓m₂ , ≈m₂
  with ~cong⟦⟧ t₁≈t₂ ~~refl-id-env
... | w₁ , w₂ , w₁~w₂ , ⇓w₁ , ⇓w₂
  with ~confl {α} w₁~w₂
... | n₁ , n₂ , n₁≡n₂ , ⇓n₁ , ⇓n₂
  with nf t₁ & nf⇓ ⇓u₁ ⇓m₁ | nf t₂ & nf⇓ ⇓u₂ ⇓m₂
... | n′ , n′≡m₁ | n′′ , n′′≡m₂
  rewrite n′ ≡ m₁ ∋ n′≡m₁ | n′′ ≡ m₂ ∋ n′′≡m₂ |
          u₁ ≡ w₁ ∋ ⟦⟧⇓-det ⇓u₁ ⇓w₁ refl |
          u₂ ≡ w₂ ∋ ⟦⟧⇓-det ⇓u₂ ⇓w₂ refl |
          m₁ ≡ n₁ ∋ quote⇓-det ⇓m₁ ⇓n₁ refl |
          m₂ ≡ n₂ ∋ quote⇓-det ⇓m₂ ⇓n₂ refl
  = n₁≡n₂
