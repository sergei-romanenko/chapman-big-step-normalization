module FiniteProducts.StrongConvertibility where

open import FiniteProducts.Utils
open import FiniteProducts.Syntax
open import FiniteProducts.Conversion
open import FiniteProducts.OPE
open import FiniteProducts.OPELemmas
open import FiniteProducts.BigStepSemantics
open import FiniteProducts.OPEBigStep
open import FiniteProducts.StrongComputability
open import FiniteProducts.StructuralNormalizer 

--
-- Now we define _~_ , a relation on values such that
--   u₁ ~ u₂ →
--     ∃₂ λ n₁ n₂ → n₁ ≡ n₂ × Quote u₁ ⇓ n₁ × Quote u₂ ⇓ n₂
--

infix 4 _~_ _~~_

_~_ : ∀ {α Γ} (u₁ u₂ : Val Γ α) → Set
_~_ {⋆} (ne us₁) (ne us₂) =
  ∃₂ λ ns₁ ns₂ → ns₁ ≡ ns₂ × Quote* us₁ ⇓ ns₁ × Quote* us₂ ⇓ ns₂
_~_ {α ⇒ β} {Γ} f₁ f₂ = ∀ {Β} (η : Β ≤ Γ) {u₁ u₂ : Val Β α} →
  u₁ ~ u₂ → ∃₂ λ w₁ w₂ →
    w₁ ~ w₂ × val≤ η f₁ ⟨∙⟩ u₁ ⇓ w₁ × val≤ η f₂ ⟨∙⟩ u₂ ⇓ w₂
_~_ {One} {Γ} u₁ u₂ = ⊤
_~_ {α * β} {Γ} u₁ u₂ =
  ∃₂ (λ f₁ f₂ → Fst u₁ ⇓ f₁ × Fst u₂ ⇓ f₂ × f₁ ~ f₂) ×
  ∃₂ (λ s₁ s₂ → Snd u₁ ⇓ s₁ × Snd u₂ ⇓ s₂ × s₁ ~ s₂)

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
    with f₁~f₂ η (~sym {α} u₁~u₂)
  ... | w₁ , w₂ , w₁~w₂ , ⇓w₁ , ⇓w₂ =
    w₂ , w₁ , ~sym {β} w₁~w₂ , ⇓w₂ , ⇓w₁
  ~sym {One} {Γ} u₁~u₂ = tt
  ~sym {α * β} {Γ}
    ((f₁ , f₂ , ⇓f₁ , ⇓f₂ , f₁~f₂) , (s₁ , s₂ , ⇓s₁ , ⇓s₂ , s₁~s₂))
    = (f₂ , f₁ , ⇓f₂ , ⇓f₁ , ~sym {α} f₁~f₂) ,
      (s₂ , s₁ , ⇓s₂ , ⇓s₁ , ~sym {β} s₁~s₂)

  ~~sym :  ∀ {Γ Δ} {ρ₁ ρ₂ : Env Γ Δ} → ρ₁ ~~ ρ₂ → ρ₂ ~~ ρ₁

  ~~sym [] = []
  ~~sym (_∷_ {α} u₁~~u₂ ρ₁~~ρ₂) =
    ~sym {α} u₁~~u₂ ∷ ~~sym ρ₁~~ρ₂

mutual

  ~trans : ∀ {α Γ} {u₁ u₂ u₃ : Val Γ α} →
    u₁ ~ u₂ → u₂ ~ u₃ → u₁ ~ u₃
  ~trans {⋆} {Γ} {ne us₁} {ne us₂} {ne us₃}
    (ns₁ , ns′ , ns₁≡ns′ , ⇓ns₁ , ⇓ns′)
    (ns′′ , ns₃ , ns′′≡ns₃ , ⇓ns′′ , ⇓ns₃)
    rewrite ns′ ≡ ns′′ ∋ quote*⇓-det ⇓ns′ ⇓ns′′ refl
    = ns₁ , ns₃ , trans ns₁≡ns′ ns′′≡ns₃ , ⇓ns₁ , ⇓ns₃
  ~trans {α ⇒ β} p q {Β} η {v₁} {v₂} v₁~v₂
    with p η (~refl′ {α} v₁~v₂) | q η v₁~v₂
  ... | w₁ , w′ , w₁~w′ , ⇓w₁ , ⇓w′ | w′′ , w₂ , w′′~w₂ , ⇓w′′ , ⇓w₂
    rewrite w′ ≡ w′′ ∋ ⟨∙⟩⇓-det ⇓w′ ⇓w′′ refl refl
    = w₁ , w₂ , ~trans {β} w₁~w′ w′′~w₂ , ⇓w₁ , ⇓w₂
  ~trans {One} p q = tt
  ~trans {α * β} {Γ} {u₁} {u′} {u₂}
    ((f₁ , f′ , ⇓f₁ , ⇓f′ , f₁~f′) , (s₁ , s′ , ⇓s₁ , ⇓s′ , s₁~s′))
    ((f′′ , f₂ , ⇓f′′ , ⇓f₂ , f′′~f₂) , (s′′ , s₂ , ⇓s′′ , ⇓s₂ , s′′~s₂))
    rewrite f′ ≡ f′′ ∋ fst⇓-det ⇓f′ ⇓f′′ refl |
            s′ ≡ s′′ ∋ snd⇓-det ⇓s′ ⇓s′′ refl
    = (f₁ , f₂ , ⇓f₁ , ⇓f₂ , ~trans {α} f₁~f′ f′′~f₂) ,
      (s₁ , s₂ , ⇓s₁ , ⇓s₂ , ~trans {β} s₁~s′ s′′~s₂)

  ~~trans : ∀ {Γ Δ} {ρ₁ ρ₂ ρ₃ : Env Γ Δ} →
    ρ₁ ~~ ρ₂ → ρ₂ ~~ ρ₃ → ρ₁ ~~ ρ₃
  ~~trans [] ρ₂~~ρ₃ = ρ₂~~ρ₃
  ~~trans (_∷_ {α} u₁~u₂ ρ₁~~ρ₂) (u₂~u₃ ∷ ρ₂~~ρ₃) =
    ~trans {α} u₁~u₂ u₂~u₃ ∷ ~~trans ρ₁~~ρ₂ ρ₂~~ρ₃

  ~refl′ : ∀ {α Γ} {u u′ : Val Γ α} → u ~ u′ → u ~ u
  ~refl′ {α} u~u′ = ~trans {α} u~u′ (~sym {α} u~u′)

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
~≤ {One} η u₁~u₂ = tt
~≤ {α * β} η
   ((f₁ , f₂ , ⇓f₁ , ⇓f₂ , f₁~f₂) , (s₁ , s₂ , ⇓s₁ , ⇓s₂ , s₁~s₂))
   = (val≤ η f₁ , val≤ η f₂ , fst⇓≤ η ⇓f₁ , fst⇓≤ η ⇓f₂ , ~≤ {α} η f₁~f₂) ,
     (val≤ η s₁ , val≤ η s₂ , snd⇓≤ η ⇓s₁ , snd⇓≤ η ⇓s₂ , ~≤ {β} η s₁~s₂)

~~≤ : ∀ {Β Γ Δ} (η : Β ≤ Γ) {ρ₁ ρ₂ : Env Γ Δ} → ρ₁ ~~ ρ₂ → 
        env≤ η ρ₁ ~~ env≤ η ρ₂
~~≤ η [] = []
~~≤ η (_∷_ {α} u₁~u₂ ρ₁~~ρ₂) = ~≤ {α} η u₁~u₂ ∷ ~~≤ η ρ₁~~ρ₂

--
-- "Confluence": u₁ ~ u₂ →
--     ∃₂ λ n₁ n₂ → n₁ ≡ n₂ × Quote u₁ ⇓ n₁ × Quote u₂ ⇓ n₂
--

mutual

  ~confl : ∀ {α Γ} {u₁ u₂ : Val Γ α} (u₁~u₂ : u₁ ~ u₂) →
    ∃₂ λ n₁ n₂ → n₁ ≡ n₂ × Quote u₁ ⇓ n₁ × Quote u₂ ⇓ n₂

  ~confl {⋆} {Γ} {ne us₁} {ne us₂} (ns₁ , ns₂ , ns₁≡ns₂ , ⇓ns₁ , ⇓ns₂) =
    ne⋆ ns₁ , ne⋆ ns₂ , cong ne⋆ ns₁≡ns₂ , ⋆⇓ us₁ ⇓ns₁ , ⋆⇓ us₂ ⇓ns₂
  ~confl {α ⇒ β} {Γ} u₁~u₂
    with u₁~u₂ wk (_~_ {α} (ne (var zero)) (ne (var zero))
         ∋ ne~ne {α} var⇓ var⇓ refl)
  ... | w₁ , w₂ , w₁~w₂ , ⇓w₁ , ⇓w₂
    with ~confl w₁~w₂
  ... | n₁ , n₂ , n₁≡n₂ , ⇓n₁ , ⇓n₂
    = lam n₁ , lam n₂ , cong lam n₁≡n₂ ,
      ⇒⇓ ⇓w₁ ⇓n₁ , ⇒⇓ ⇓w₂ ⇓n₂
  ~confl {One} u₁~u₂ =
    void , void , refl , One⇓ , One⇓
  ~confl {α * β}
    ((f₁ , f₂ , ⇓f₁ , ⇓f₂ , f₁~f₂) , (s₁ , s₂ , ⇓s₁ , ⇓s₂ , s₁~s₂))
    with ~confl f₁~f₂ | ~confl s₁~s₂
  ... | na₁ , na₂ , na₁≡na₂ , ⇓na₁ , ⇓na₂ | nb₁ , nb₂ , nb₁≡nb₂ , ⇓nb₁ , ⇓nb₂
    = pair na₁ nb₁ , pair na₂ nb₂ , cong₂ pair na₁≡na₂ nb₁≡nb₂ ,
      Prod⇓ ⇓f₁ ⇓na₁ ⇓s₁ ⇓nb₁ , Prod⇓ ⇓f₂ ⇓na₂ ⇓s₂ ⇓nb₂

  ne~ne : ∀ {α Γ}
    {us₁ : NeVal Γ α} {ns₁} (⇓ns₁ : Quote* us₁ ⇓ ns₁)
    {us₂ : NeVal Γ α} {ns₂} (⇓ns₂ : Quote* us₂ ⇓ ns₂)
    (ns₁≡ns₂ : ns₁ ≡ ns₂) →
    ne us₁ ~ ne us₂
  ne~ne {⋆} {Γ} {us₁} {ns₁} ⇓ns₁ {us₂} {ns₂} ⇓ns₂ ns₁≡ns₂ =
    ns₁ , ns₂ , ns₁≡ns₂ , ⇓ns₁ , ⇓ns₂
  ne~ne {α ⇒ β} {Γ} {us₁} {ns₁} ⇓ns₁ {us₂} {ns₂} ⇓ns₂ ns₁≡ns₂
                {Β} η {v₁} {v₂} v₁~v₂
    with ~confl v₁~v₂
  ... | n₁ , n₂ , n₁≡n₂ , ⇓n₁ , ⇓n₂
    with ne (app (neVal≤ η us₁) v₁) ~ ne (app (neVal≤ η us₂) v₂) ∋
      ne~ne {β}
           (app⇓ (quote*≤ η ⇓ns₁) ⇓n₁)
           (app⇓ (quote*≤ η ⇓ns₂) ⇓n₂)
           (cong₂ app (cong (neNf≤ η) ns₁≡ns₂) n₁≡n₂)
  ... | us₁-v₁~us₂-v₂
    = ne (app (neVal≤ η us₁) v₁) , ne (app (neVal≤ η us₂) v₂) ,
         us₁-v₁~us₂-v₂ , ne⇓ , ne⇓
  ne~ne {One} {Γ} {us₁} {ns₁} ⇓ns₁ {us₂} {ns₂} ⇓ns₂ ns₁≡ns₂ =
    tt
  ne~ne {α * β} {Γ} {us₁} {ns₁} ⇓ns₁ {us₂} {ns₂} ⇓ns₂ ns₁≡ns₂
    = (ne (fst us₁) , ne (fst us₂) , fst-ne⇓ , fst-ne⇓ ,
          ne~ne (fst⇓ ⇓ns₁) (fst⇓ ⇓ns₂) (cong fst ns₁≡ns₂)) ,
      (ne (snd us₁) , ne (snd us₂) , snd-ne⇓ , snd-ne⇓ ,
          ne~ne (snd⇓ ⇓ns₁) (snd⇓ ⇓ns₂) (cong snd ns₁≡ns₂))

-- id-env ~~ id-env

~~refl-id-env : ∀ {Γ} → id-env {Γ} ~~ id-env
~~refl-id-env {[]} = []
~~refl-id-env {γ ∷ Γ} =
  ne~ne {γ} var⇓ var⇓ refl ∷ ~~≤ wk ~~refl-id-env
