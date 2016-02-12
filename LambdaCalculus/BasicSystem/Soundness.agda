module BasicSystem.Soundness where

open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.Conversion
open import BasicSystem.OPE
open import BasicSystem.OPELemmas
open import BasicSystem.BigStepSemantics
open import BasicSystem.OPEBigStep
open import BasicSystem.StrongComputability
open import BasicSystem.StructuralNormaliser 


--
-- Soundness: t₁ ≈ t₂ → nf t₁ ≡ nf t₂
-- (Normalisation takes convertible terms to identical normal forms.)
--

infix 4 _~_ _~~_

_~_ : ∀ {α Γ} (u₁ u₂ : Val Γ α) → Set
_~_ {⋆} (ne us₁) (ne us₂) =
  ∃₂ λ ns₁ ns₂ → ns₁ ≡ ns₂ × Quote* us₁ ⇓ ns₁ × Quote* us₂ ⇓ ns₂
_~_ {α ⇒ β} {Γ} f₁ f₂ = ∀ {Β} (η : Β ≤ Γ) {u₁ u₂ : Val Β α} →
  u₁ ~ u₂ → ∃₂ λ w₁ w₂ →
    w₁ ~ w₂ × val≤ η f₁ ⟨∙⟩ u₁ ⇓ w₁ × val≤ η f₂ ⟨∙⟩ u₂ ⇓ w₂

data _~~_ : ∀ {Γ Δ} (ρ₁ ρ₂ : Env Γ Δ) → Set where
  [] :  ∀ {Γ} →
    _~~_ {Γ} [] []
  _∷_ : ∀ {α Γ Δ} {u₁ u₂ : Val Γ α} {ρ₁ ρ₂ : Env Γ Δ} →
    u₁ ~ u₂ → ρ₁ ~~ ρ₂ →
    u₁ ∷ ρ₁ ~~ u₂ ∷ ρ₂

module DifferentValuesMayBeEquivalent where

  -- The subtle point is that two different values may have
  -- identical  normal forms.

  val-III : Val [] (⋆ ⇒ ⋆)
  val-III = lam ø []

  val-SKK : Val [] (⋆ ⇒ ⋆)
  val-SKK =
    lam (ø [ ↑ ] [ ↑ ] ∙ ø ∙ (ø [ ↑ ] ∙ ø))
      (lam {⋆} {⋆ ⇒ ⋆} (ƛ ø [ ↑ ]) [] ∷ (lam (ƛ ø [ ↑ ]) [] ∷ []))

  val-III~val-III : val-III ~ val-III
  val-III~val-III {Β} η {u₁} {u₂} u₁~u₂ =
    u₁ , u₂ , u₁~u₂ , lam⇓ ø⇓ , lam⇓ ø⇓

mutual

  ~sym : ∀ {α Γ} {u₁ u₂ : Val Γ α} → u₁ ~ u₂ → u₂ ~ u₁

  ~sym {⋆} {Γ} {ne us₁} {ne us₂} (ns₁ , ns₂ , ns₁≡ns₂ , ⇓ns₁ , ⇓ns₂) =
    ns₂ , ns₁ , sym ns₁≡ns₂ , ⇓ns₂ , ⇓ns₁
  ~sym {α ⇒ β} {Γ} f₁~f₂ {B} η {u₁} {u₂} u₁~u₂
    with f₁~f₂ η (~sym u₁~u₂)
  ... | w₁ , w₂ , w₁~w₂ , ⇓w₁ , ⇓w₂ =
    w₂ , w₁ , ~sym w₁~w₂ , ⇓w₂ , ⇓w₁

  ~~sym :  ∀ {Γ Δ} {ρ₁ ρ₂ : Env Γ Δ} → ρ₁ ~~ ρ₂ → ρ₂ ~~ ρ₁

  ~~sym [] = []
  ~~sym (u₁~~u₂ ∷ ρ₁~~ρ₂) =
    ~sym u₁~~u₂ ∷ ~~sym ρ₁~~ρ₂

mutual

  ~trans : ∀ {α Γ} {u₁ u₂ u₃ : Val Γ α} →
    u₁ ~ u₂ → u₂ ~ u₃ → u₁ ~ u₃
  ~trans {⋆} {Γ} {ne us₁} {ne us₂} {ne us₃}
    (ns₁ , ns′ , ns₁≡ns′ , ⇓ns₁ , ⇓ns′)
    (ns′′ , ns₃ , ns′′≡ns₃ , ⇓ns′′ , ⇓ns₃)
    rewrite ns′ ≡ ns′′ ∋ quote*⇓-det ⇓ns′ ⇓ns′′ refl
    = ns₁ , ns₃ , trans ns₁≡ns′ ns′′≡ns₃ , ⇓ns₁ , ⇓ns₃
  ~trans {α ⇒ β} p q {Β} η {v₁} {v₂} v₁~v₂
    with p η (~refl′ v₁~v₂) | q η v₁~v₂
  ... | w₁ , w′ , w₁~w′ , ⇓w₁ , ⇓w′ | w′′ , w₂ , w′′~w₂ , ⇓w′′ , ⇓w₂
    rewrite w′ ≡ w′′ ∋ ⟨∙⟩⇓-det ⇓w′ ⇓w′′ refl refl
    = w₁ , w₂ , ~trans w₁~w′ w′′~w₂ , ⇓w₁ , ⇓w₂

  ~~trans : ∀ {Γ Δ} {ρ₁ ρ₂ ρ₃ : Env Γ Δ} →
    ρ₁ ~~ ρ₂ → ρ₂ ~~ ρ₃ → ρ₁ ~~ ρ₃
  ~~trans [] ρ₂~~ρ₃ = ρ₂~~ρ₃
  ~~trans (u₁~u₂ ∷ ρ₁~~ρ₂) (u₂~u₃ ∷ ρ₂~~ρ₃) =
    ~trans u₁~u₂ u₂~u₃ ∷ ~~trans ρ₁~~ρ₂ ρ₂~~ρ₃

  ~refl′ : ∀ {α Γ} {u u′ : Val Γ α} → u ~ u′ → u ~ u
  ~refl′ u~u′ = ~trans u~u′ (~sym u~u′)

  ~~refl′ : ∀ {Γ Δ} {ρ ρ′ : Env Γ Δ} → ρ ~~ ρ′ → ρ ~~ ρ
  ~~refl′ ρ~~ρ′ = ~~trans ρ~~ρ′ (~~sym ρ~~ρ′)

--
-- u₁ ~ u₂ → val≤ η u₁ ~ val≤ η u₂
-- ρ₁ ~~ ρ₂ → env≤ η ρ₁ ~~ env≤ η ρ₂
--

~≤ : ∀ {α Γ Δ} (η : Γ ≤ Δ) {u₁ u₂ : Val Δ α} → u₁ ~ u₂ →
       val≤ η u₁ ~ val≤ η u₂
~≤ {⋆} η {ne us₁} {ne us₂} (ns₁ , ns₂ , ns₁≡ns₂ , ⇓ns₁ , ⇓ns₂) =
  neNf≤ η ns₁ , neNf≤ η ns₂ , cong (neNf≤ η) ns₁≡ns₂ ,
    quote*≤ η ⇓ns₁ , quote*≤ η ⇓ns₂
~≤ {α ⇒ β} η {u₁} {u₂} p {B} η′ {v₁} {v₂} v₁~v₂
  with p (η′ ● η) v₁~v₂
... | w₁ , w₂ , w₁~w₂ , ⇓w₁ , ⇓w₂
  rewrite val≤ η′ (val≤ η u₁) ≡ val≤ (η′ ● η) u₁ ∋ val≤∘ η′ η u₁ |
          val≤ η′ (val≤ η u₂) ≡ val≤ (η′ ● η) u₂ ∋ val≤∘ η′ η u₂
  = w₁ , w₂ , w₁~w₂ , ⇓w₁ , ⇓w₂

~~≤ : ∀ {Β Γ Δ} (η : Β ≤ Γ) {ρ₁ ρ₂ : Env Γ Δ} → ρ₁ ~~ ρ₂ → 
        env≤ η ρ₁ ~~ env≤ η ρ₂
~~≤ η [] = []
~~≤ η (u₁~u₂ ∷ ρ₁~~ρ₂) = ~≤ η u₁~u₂ ∷ ~~≤ η ρ₁~~ρ₂

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
  ~cong⟦⟧ (≈sym t₁≈t₂) ρ₁~~ρ₂
    with ~cong⟦⟧ t₁≈t₂ (~~sym ρ₁~~ρ₂)
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂
    = u₂ , u₁ , ~sym u₁~u₂ , ⇓u₂ , ⇓u₁
  ~cong⟦⟧ (≈trans t₁≈t₂ t₂≈t₃) ρ₁~~ρ₂
    with ~cong⟦⟧ t₁≈t₂ (~~refl′ ρ₁~~ρ₂) | ~cong⟦⟧ t₂≈t₃ ρ₁~~ρ₂
  ... | u₁ , u₂ , u₁~u₂ , ⇓u₁ , ⇓u₂ | v₁ , v₂ , v₁~v₂ , ⇓v₁ , ⇓v₂
    rewrite u₂ ≡ v₁ ∋ ⟦⟧⇓-det ⇓u₂ ⇓v₁ refl
    = u₁ , v₂ , ~trans u₁~u₂ v₁~v₂ , ⇓u₁ , ⇓v₂
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
-- "Confluence": u₁ ~ u₂ →
--     ∃₂ λ n₁ n₂ → n₁ ≡ n₂ × Quote u₁ ⇓ n₁ × Quote u₂ ⇓ n₂
--

  ~confl : ∀ {α Γ} (u₁ u₂ : Val Γ α) (u₁~u₂ : u₁ ~ u₂) →
    ∃₂ λ n₁ n₂ → n₁ ≡ n₂ × Quote u₁ ⇓ n₁ × Quote u₂ ⇓ n₂

  ~confl {⋆} (ne us₁) (ne us₂) (ns₁ , ns₂ , ns₁≡ns₂ , ⇓ns₁ , ⇓ns₂) =
    ne ns₁ , ne ns₂ , cong ne ns₁≡ns₂ , ⋆⇓ us₁ ⇓ns₁ , ⋆⇓ us₂ ⇓ns₂
  ~confl {α ⇒ β} {Γ} u₁ u₂ u₁~u₂
    with u₁~u₂ wk (_~_ {α} (ne (var zero)) (ne (var zero))
         ∋ confl-ne→~ {α} var⇓ var⇓ refl)
  ... | w₁ , w₂ , w₁~w₂ , ⇓w₁ , ⇓w₂
    with ~confl w₁ w₂ w₁~w₂
  ... | n₁ , n₂ , n₁≡n₂ , ⇓n₁ , ⇓n₂
    = lam n₁ , lam n₂ , cong lam n₁≡n₂ ,
      ⇒⇓ ⇓w₁ ⇓n₁ , ⇒⇓ ⇓w₂ ⇓n₂

  confl-ne→~ : ∀ {α Γ}
    {us₁ : NeVal Γ α} {ns₁} (⇓ns₁ : Quote* us₁ ⇓ ns₁)
    {us₂ : NeVal Γ α} {ns₂} (⇓ns₂ : Quote* us₂ ⇓ ns₂)
    (ns₁≡ns₂ : ns₁ ≡ ns₂) →
    ne us₁ ~ ne us₂
  confl-ne→~ {⋆} {Γ} {us₁} {ns₁} ⇓ns₁ {us₂} {ns₂} ⇓ns₂ ns₁≡ns₂ =
    ns₁ , ns₂ , ns₁≡ns₂ , ⇓ns₁ , ⇓ns₂
  confl-ne→~ {α ⇒ β} {Γ} {us₁} {ns₁} ⇓ns₁ {us₂} {ns₂} ⇓ns₂ ns₁≡ns₂
                {Β} η {v₁} {v₂} v₁~v₂
    with ~confl v₁ v₂ v₁~v₂
  ... | n₁ , n₂ , n₁≡n₂ , ⇓n₁ , ⇓n₂
    with ne (app (neVal≤ η us₁) v₁) ~ ne (app (neVal≤ η us₂) v₂) ∋
      confl-ne→~ {β}
           (app⇓ (quote*≤ η ⇓ns₁) ⇓n₁)
           (app⇓ (quote*≤ η ⇓ns₂) ⇓n₂)
           (cong₂ app (cong (neNf≤ η) ns₁≡ns₂) n₁≡n₂)
  ... | us₁-v₁~us₂-v₂
    = ne (app (neVal≤ η us₁) v₁) , ne (app (neVal≤ η us₂) v₂) ,
         us₁-v₁~us₂-v₂ , ne⇓ , ne⇓

-- id-env ~~ id-env

~~refl-id-env : ∀ {Γ} → id-env {Γ} ~~ id-env
~~refl-id-env {[]} = []
~~refl-id-env {γ ∷ Γ} =
  confl-ne→~ var⇓ var⇓ refl ∷ ~~≤ wk ~~refl-id-env

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
  with ~confl w₁ w₂ w₁~w₂
... | n₁ , n₂ , n₁≡n₂ , ⇓n₁ , ⇓n₂
  with nf t₁ & nf⇓ ⇓u₁ ⇓m₁ | nf t₂ & nf⇓ ⇓u₂ ⇓m₂
... | n′ , n′≡m₁ | n′′ , n′′≡m₂
  rewrite n′ ≡ m₁ ∋ n′≡m₁ | n′′ ≡ m₂ ∋ n′′≡m₂ |
          u₁ ≡ w₁ ∋ ⟦⟧⇓-det ⇓u₁ ⇓w₁ refl |
          u₂ ≡ w₂ ∋ ⟦⟧⇓-det ⇓u₂ ⇓w₂ refl |
          m₁ ≡ n₁ ∋ quote⇓-det ⇓m₁ ⇓n₁ refl |
          m₂ ≡ n₂ ∋ quote⇓-det ⇓m₂ ⇓n₂ refl
  = n₁≡n₂
