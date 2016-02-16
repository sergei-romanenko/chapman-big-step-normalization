module FullSystem.BigStepSemantics where

open import FullSystem.Utils
open import FullSystem.Syntax
open import FullSystem.OPE

--
-- Relational big-step semantics.
--

mutual

  infix 4 ⟦_⟧_⇓_ ⟦_⟧*_⇓_ _⟨∙⟩_⇓_

  data ⟦_⟧_⇓_ : ∀ {α Γ Δ} (t : Tm Δ α) (ρ : Env Γ Δ) (u : Val Γ α) → Set where
    ø⇓ : ∀ {α Γ Δ} {u : Val Γ α} {ρ : Env Γ Δ} →
      ⟦ ø ⟧ (u ∷ ρ) ⇓ u
    ∙⇓ : ∀ {α β Γ Δ} {t : Tm Δ (α ⇒ β)} {t′ : Tm Δ α} {ρ : Env Γ Δ} {u v w}
      (⇓u : ⟦ t ⟧ ρ ⇓ u) (⇓v : ⟦ t′ ⟧ ρ ⇓ v) (⇓w : u ⟨∙⟩ v ⇓ w) →
      ⟦ t ∙ t′ ⟧ ρ ⇓ w
    ƛ⇓ : ∀ {α β Γ Δ} {t : Tm (α ∷ Δ) β} {ρ : Env Γ Δ} →
      ⟦ ƛ t ⟧ ρ ⇓ lam t ρ
    []⇓ : ∀ {α Γ Δ Δ′} {t : Tm Δ′ α } {σ : Sub Δ Δ′} {ρ : Env Γ Δ} {θ u}
      (⇓θ : ⟦ σ ⟧* ρ ⇓ θ) (⇓u : ⟦ t ⟧ θ ⇓ u) →
      ⟦ t [ σ ] ⟧ ρ ⇓ u
    void⇓ : ∀ {Γ Δ} {ρ : Env Γ Δ} →
      ⟦ void ⟧ ρ ⇓ void
    pair⇓ : ∀ {α β Γ Δ} {f : Tm Δ α} {s : Tm Δ β} {ρ : Env Γ Δ}
      {u} (⇓u : ⟦ f ⟧ ρ ⇓ u) {v} (⇓v : ⟦ s ⟧ ρ ⇓ v) →
      ⟦ pair f s ⟧ ρ ⇓ pair u v
    fst⇓ : ∀ {α β Γ Δ} {t : Tm Δ (α * β)} {ρ : Env Γ Δ}
      {uv} (⇓uv : ⟦ t ⟧ ρ ⇓ uv) {w} (⇓w : Fst uv ⇓ w) →
      ⟦ fst t ⟧ ρ ⇓ w 
    snd⇓ : ∀ {α β Γ Δ} {t : Tm Δ (α * β)} {ρ : Env Γ Δ}
      {uv} (⇓uv : ⟦ t ⟧ ρ ⇓ uv) {w} (⇓w : Snd uv ⇓ w) → 
       ⟦ snd t ⟧ ρ ⇓ w 
    zero⇓ : ∀ {Γ Δ} {ρ : Env Γ Δ} → ⟦ zero ⟧ ρ ⇓ zero
    suc⇓  : ∀ {Γ Δ} {t : Tm Δ N} {ρ : Env Γ Δ} {u} (⇓u : ⟦ t ⟧ ρ ⇓ u) →
      ⟦ suc t ⟧ ρ ⇓ suc u
    prim⇓ : ∀ {α Γ Δ} {a : Tm Δ α} {b k} {ρ : Env Γ Δ} {u v w z}
      (⇓u : ⟦ a ⟧ ρ ⇓ u) (⇓v : ⟦ b ⟧  ρ ⇓ v) (⇓w : ⟦ k ⟧  ρ ⇓ w)
      (⇓z : Prim u & v & w ⇓ z) →
      ⟦ prim a b k ⟧ ρ ⇓ z

  data ⟦_⟧*_⇓_ : ∀ {Γ Δ Δ′} (σ : Sub Δ Δ′) (ρ : Env Γ Δ) (θ : Env Γ Δ′) →
       Set where
    ι⇓ : ∀ {Γ Σ} {ρ : Env Γ Σ} →
      ⟦ ı ⟧* ρ ⇓ ρ
    ○⇓ : ∀ {Γ Δ Δ′ Δ′′} {σ : Sub Δ′ Δ′′} {σ′ : Sub Δ Δ′} {ρ : Env Γ Δ} {θ₁ θ₂}
      (⇓θ₁ : ⟦ σ′ ⟧* ρ ⇓ θ₁) (⇓θ₂ : ⟦ σ ⟧* θ₁ ⇓ θ₂) →
      ⟦ σ ○ σ′ ⟧* ρ ⇓ θ₂
    ∷⇓ : ∀ {α Γ Δ Δ′} {t : Tm Δ α} {σ : Sub Δ Δ′} {ρ : Env Γ Δ} {u θ}
      (⇓u : ⟦ t ⟧ ρ ⇓ u) (⇓θ : ⟦ σ ⟧* ρ ⇓ θ) →
      ⟦ t ∷ σ ⟧* ρ ⇓ (u ∷ θ)
    ↑⇓ : ∀ {α Γ Δ} {u : Val Γ α} {ρ : Env Γ Δ} →
      ⟦ ↑ ⟧* (u ∷ ρ) ⇓ ρ

  data _⟨∙⟩_⇓_ : ∀ {α β Γ}
       (u : Val Γ (α ⇒ β)) (v : Val Γ α) (w : Val Γ β) → Set where
    ne⇓  : ∀ {α β Γ} {us : NeVal Γ (α ⇒ β)} {u} →
      ne us ⟨∙⟩ u ⇓ ne (app us u)
    lam⇓ : ∀ {α β Γ Δ} {t : Tm (α ∷ Δ) β} {ρ : Env Γ Δ} {u v}
      (⇓v : ⟦ t ⟧ (u ∷ ρ) ⇓ v) →
      lam t ρ ⟨∙⟩ u ⇓ v

  data Fst_⇓_ : ∀ {α β Γ} (uv : Val Γ (α * β)) (v : Val Γ α) → Set where
    fst-pair⇓ : ∀ {α β Γ} {u : Val Γ α} {v : Val Γ β} →
      Fst (pair u v) ⇓ u
    fst-ne⇓ : ∀ {Γ α β} {ns : NeVal Γ (α * β)} →
      Fst (ne ns) ⇓ ne (fst ns) 

  data Snd_⇓_ : ∀ {α β Γ} (uv : Val Γ (α * β)) (v : Val Γ β) → Set where
    snd-pair⇓ : ∀ {α β Γ} {u : Val Γ α} {v : Val Γ β} →
      Snd (pair u  v) ⇓ v
    snd-ne⇓ : ∀ {Γ α β} {ns : NeVal Γ (α * β)} →
      Snd (ne ns) ⇓ ne (snd ns) 

  data Prim_&_&_⇓_ : ∀ {α Γ} (u : Val Γ α) (v : Val Γ (N ⇒ α ⇒ α))
                   (w : Val Γ N) (w′ : Val Γ α) → Set where
    primn⇓ : ∀ {α Γ} {u : Val Γ α} {v us} →
      Prim u & v & ne us ⇓ ne (prim u v us)
    primz⇓ : ∀ {α Γ} {u : Val Γ α} {v} →
      Prim u & v & zero ⇓ u
    prims⇓ : ∀ {α Γ} {u : Val Γ α} {v w vw z vwz}
      (⇓vw : v ⟨∙⟩ w ⇓ vw) (⇓w′ : Prim u & v & w ⇓ z)
      (⇓vwz :  vw ⟨∙⟩ z ⇓ vwz) →
      Prim u & v & suc w ⇓ vwz


mutual

  data Quote_⇓_ : ∀ {α Γ} (u : Val Γ α) (n : Nf Γ α) → Set where
    ⋆⇓ : ∀ {Γ} (us : NeVal Γ ⋆) {ns}
      (⇓ns : Quote* us ⇓ ns) →
      Quote (ne us) ⇓ ne⋆ ns
    ⇒⇓ : ∀ {α β Γ} {f : Val Γ (α ⇒ β)} {u n} →
      (⇓u : val≤ wk f ⟨∙⟩ ne (var zero) ⇓ u) (⇓n : Quote u ⇓ n) →
      Quote f ⇓ lam n
    One⇓ : ∀ {Γ} {u : Val Γ One} →
      Quote u ⇓ void
    Prod⇓ : ∀ {α β Γ} {uv : Val Γ (α * β)}
      {u} (⇓u : Fst uv ⇓ u) {nu} (⇓na : Quote u ⇓ nu)
      {v} (⇓v : Snd uv ⇓ v) {nv} (⇓nb : Quote v ⇓ nv) →
      Quote uv ⇓ pair nu nv
    N⇓ : ∀ {Γ} {us : NeVal Γ N} {ns : NeNf Γ N} (⇓ns : Quote* us ⇓ ns) →
      Quote ne us ⇓ neN ns
    zero⇓ : ∀ {Γ} →
      Quote zero {Γ} ⇓ zero
    suc⇓  : ∀ {Γ} {u : Val Γ N} {n : Nf Γ N} (⇓n : Quote u ⇓ n) →
      Quote suc u ⇓ suc n 

  data Quote*_⇓_ : ∀ {α Γ} (us : NeVal Γ α) (ns : NeNf Γ α) → Set where
    var⇓ : ∀ {α Γ} {x : Var Γ α} →
      Quote* var x ⇓ var x
    app⇓ : ∀ {α β Γ} {us : NeVal Γ (α ⇒ β)} {u : Val Γ α} {ns n}
      (⇓ns : Quote* us ⇓ ns) (⇓n : Quote u ⇓ n) →
      Quote* app us u ⇓ app ns n
    fst⇓ : ∀ {α β Γ} {u : NeVal Γ (α * β)} {n} →
      Quote* u ⇓ n → Quote* fst u ⇓ fst n
    snd⇓ : ∀ {Γ α β} {u : NeVal Γ (α * β)} {n} →
      Quote* u ⇓ n → Quote* snd u ⇓ snd n
    prim⇓ : ∀ {α Γ} {u : Val Γ α} {v w nu nv nw}
      (⇓nu : Quote u ⇓ nu) (⇓nv : Quote v ⇓ nv) (⇓nw : Quote* w ⇓ nw) → 
      Quote* prim u v w ⇓ prim nu nv nw


data Nf_⇓_ : ∀ {α Γ} (t : Tm Γ α) (n : Nf Γ α) → Set where
  nf⇓ : ∀ {α Γ} {t : Tm Γ α} {u n}
    (⇓u : ⟦ t ⟧ id-env ⇓ u) (⇓n : Quote u ⇓ n) →
    Nf t ⇓ n

--
-- Determinism (left-injectivity) of ⟦_⟧_⇓_ , Quote_⇓_ and Nf_⇓_ :
--
--   ⟦ t ⟧ ρ₁ ⇓ u₁ →  ⟦ t ⟧ ρ₂ ⇓ u₂ → ρ₁ ≡ ρ₂ → u₁ ≡ u₂
--   Quote u₁ ⇓ n₁ →  Quote u₂ ⇓ n₂ → u₁ ≡ u₂ →  n₁ ≡ n₂
--   Nf t ⇓ n₁ → Nf t ⇓ n₂ → n₁ ≡ n₂
--

--   ⟦ t ⟧ ρ₁ ⇓ u₁ →  ⟦ t ⟧ ρ₂ ⇓ u₂ → ρ₁ ≡ ρ₂ → u₁ ≡ u₂

mutual

  ⟦⟧⇓-det : ∀ {α Γ Δ} {t : Tm Δ α} {ρ₁ ρ₂ : Env Γ Δ} {u₁ u₂} →
    (⇓u₁ : ⟦ t ⟧ ρ₁ ⇓ u₁) (⇓u₂ : ⟦ t ⟧ ρ₂ ⇓ u₂)
    (ρ₁≡ρ₂ : ρ₁ ≡ ρ₂) → u₁ ≡ u₂

  ⟦⟧⇓-det ø⇓ ø⇓ refl = refl
  ⟦⟧⇓-det (∙⇓ ⇓u₁ ⇓v₁ ⇓w₁) (∙⇓ ⇓u₂ ⇓v₂ ⇓w₂) ρ₁≡ρ₂ =
    ⟨∙⟩⇓-det ⇓w₁ ⇓w₂ (⟦⟧⇓-det ⇓u₁ ⇓u₂ ρ₁≡ρ₂) (⟦⟧⇓-det ⇓v₁ ⇓v₂ ρ₁≡ρ₂)
  ⟦⟧⇓-det ƛ⇓ ƛ⇓ refl = refl
  ⟦⟧⇓-det ([]⇓ ⇓ρ₁ ⇓u₁) ([]⇓ ⇓ρ₂ ⇓u₂) ρ₁≡ρ₂ =
    ⟦⟧⇓-det ⇓u₁ ⇓u₂ (⟦⟧*⇓-det ⇓ρ₁ ⇓ρ₂ ρ₁≡ρ₂)
  ⟦⟧⇓-det void⇓ void⇓ ρ₁≡ρ₂ = refl
  ⟦⟧⇓-det (pair⇓ ⇓u₁ ⇓v₁) (pair⇓ ⇓u₂ ⇓v₂) ρ₁≡ρ₂ =
    cong₂ pair (⟦⟧⇓-det ⇓u₁ ⇓u₂ ρ₁≡ρ₂) (⟦⟧⇓-det ⇓v₁ ⇓v₂ ρ₁≡ρ₂)
  ⟦⟧⇓-det (fst⇓ ⇓u₁ ⇓w₁) (fst⇓ ⇓u₂ ⇓w₂) ρ₁≡ρ₂ =
    fst⇓-det ⇓w₁ ⇓w₂ (⟦⟧⇓-det ⇓u₁ ⇓u₂ ρ₁≡ρ₂)
  ⟦⟧⇓-det (snd⇓ ⇓u₁ ⇓w₁) (snd⇓ ⇓u₂ ⇓w₂) ρ₁≡ρ₂ =
    snd⇓-det ⇓w₁ ⇓w₂ (⟦⟧⇓-det ⇓u₁ ⇓u₂ ρ₁≡ρ₂)
  ⟦⟧⇓-det zero⇓ zero⇓ ρ₁≡ρ₂ =
    refl
  ⟦⟧⇓-det (suc⇓ ⇓u₁) (suc⇓ ⇓u₂) ρ₁≡ρ₂ =
    cong suc (⟦⟧⇓-det ⇓u₁ ⇓u₂ ρ₁≡ρ₂)
  ⟦⟧⇓-det (prim⇓ ⇓u₁ ⇓v₁ ⇓w₁ ⇓w′₁) (prim⇓ ⇓u₂ ⇓v₂ ⇓w₂ ⇓w′₂) ρ₁≡ρ₂ =
    prim⇓-det ⇓w′₁ ⇓w′₂ (⟦⟧⇓-det ⇓u₁ ⇓u₂ ρ₁≡ρ₂) (⟦⟧⇓-det ⇓v₁ ⇓v₂ ρ₁≡ρ₂)
                        (⟦⟧⇓-det ⇓w₁ ⇓w₂ ρ₁≡ρ₂)

  ⟦⟧*⇓-det : ∀ {Γ Δ Δ′} {σ : Sub Δ Δ′} {ρ₁ ρ₂ : Env Γ Δ} {θ₁ θ₂}
    (⇓θ₁ : ⟦ σ ⟧* ρ₁ ⇓ θ₁) (⇓θ₂ : ⟦ σ ⟧* ρ₂ ⇓ θ₂)
    (ρ₁≡ρ₂ : ρ₁ ≡ ρ₂) → θ₁ ≡ θ₂

  ⟦⟧*⇓-det ι⇓ ι⇓ ρ₁≡ρ₂ = ρ₁≡ρ₂
  ⟦⟧*⇓-det (○⇓ ⇓θ₁ ⇓θ₂) (○⇓ ⇓φ₁ ⇓φ₂) ρ₁≡ρ₂ =
    ⟦⟧*⇓-det ⇓θ₂ ⇓φ₂ (⟦⟧*⇓-det ⇓θ₁ ⇓φ₁ ρ₁≡ρ₂)
  ⟦⟧*⇓-det (∷⇓ ⇓u₁ ⇓θ₁) (∷⇓ ⇓u₂ ⇓θ₂) ρ₁≡ρ₂ =
    cong₂ _∷_ (⟦⟧⇓-det ⇓u₁ ⇓u₂ ρ₁≡ρ₂) (⟦⟧*⇓-det ⇓θ₁ ⇓θ₂ ρ₁≡ρ₂)
  ⟦⟧*⇓-det ↑⇓ ↑⇓ refl = refl


  ⟨∙⟩⇓-det : ∀ {α β Γ} {u₁ u₂ : Val Γ (α ⇒ β)} {v₁ v₂ : Val Γ α} {w₁ w₂}
    (⇓w₁ : u₁ ⟨∙⟩ v₁ ⇓ w₁) (⇓w₂ : u₂ ⟨∙⟩ v₂ ⇓ w₂)
    (u₁≡u₂ : u₁ ≡ u₂) (v₁≡v₂ : v₁ ≡ v₂) → w₁ ≡ w₂

  ⟨∙⟩⇓-det ne⇓ ne⇓ refl refl = refl
  ⟨∙⟩⇓-det (lam⇓ ⇓w₁) (lam⇓ ⇓w₂) refl refl =
    ⟦⟧⇓-det ⇓w₁ ⇓w₂ refl

  fst⇓-det : ∀ {α β Γ} {u₁ u₂ : Val Γ (α * β)} {w₁ w₂}
    (⇓w₁ : Fst u₁ ⇓ w₁) (⇓w₂ : Fst u₂ ⇓ w₂)
    (u₁≡u₂ : u₁ ≡ u₂) → w₁ ≡ w₂
  fst⇓-det fst-pair⇓ fst-pair⇓ refl = refl
  fst⇓-det fst-ne⇓ fst-ne⇓ refl = refl

  snd⇓-det : ∀ {α β Γ} {u₁ u₂ : Val Γ (α * β)} {w₁ w₂}
    (⇓w₁ : Snd u₁ ⇓ w₁) (⇓w₂ : Snd u₂ ⇓ w₂)
    (u₁≡u₂ : u₁ ≡ u₂) → w₁ ≡ w₂
  snd⇓-det snd-pair⇓ snd-pair⇓ refl = refl
  snd⇓-det snd-ne⇓ snd-ne⇓ refl = refl

  prim⇓-det : ∀ {α Γ} {u₁ u₂ : Val Γ α} {v₁ v₂ : Val Γ (N ⇒ α ⇒ α)}
    {w₁ w₂ : Val Γ N} {w′₁ w′₂}
    (⇓w′₁ : Prim u₁ & v₁ & w₁ ⇓ w′₁) (⇓w′₂ : Prim u₂ & v₂ & w₂ ⇓ w′₂)
    (u₁≡u₂ : u₁ ≡ u₂) (v₁≡v₂ : v₁ ≡ v₂) (w₁≡w₂ : w₁ ≡ w₂) →
    w′₁ ≡ w′₂
  prim⇓-det primn⇓ primn⇓ refl refl refl = refl
  prim⇓-det primz⇓ primz⇓ refl refl refl = refl
  prim⇓-det (prims⇓ ⇓vw₁ ⇓w′₁ ⇓vww′₁) (prims⇓ ⇓vw₂ ⇓w′₂ ⇓vww′₂)
    refl refl refl
    = ⟨∙⟩⇓-det ⇓vww′₁ ⇓vww′₂
               (⟨∙⟩⇓-det ⇓vw₁ ⇓vw₂ refl refl)
               (prim⇓-det ⇓w′₁ ⇓w′₂ refl refl refl)

--   Quote u₁ ⇓ n₁ →  Quote u₂ ⇓ n₂ → u₁ ≡ u₂ →  n₁ ≡ n₂

mutual

  quote⇓-det : ∀ {α Γ} {u₁ u₂ : Val Γ α} {n₁ n₂}
    (⇓n₁ : Quote u₁ ⇓ n₁) (⇓n₂ : Quote u₂ ⇓ n₂)
    (u₁≡u₂ : u₁ ≡ u₂) →
    n₁ ≡ n₂
  quote⇓-det (⋆⇓ us₁ ⇓ns₁) (⋆⇓ .us₁ ⇓ns₂) refl =
    cong ne⋆ (quote*⇓-det ⇓ns₁ ⇓ns₂ refl)
  quote⇓-det (⇒⇓ ⇓u₁ ⇓n₁) (⇒⇓ ⇓u₂ ⇓n₂) refl =
    cong lam (quote⇓-det ⇓n₁ ⇓n₂ (⟨∙⟩⇓-det ⇓u₁ ⇓u₂ refl refl))
  quote⇓-det One⇓ One⇓ refl = refl
  quote⇓-det (Prod⇓ ⇓u₁ ⇓na₁ ⇓v₁ ⇓nb₁) (Prod⇓ ⇓u₂ ⇓na₂ ⇓v₂ ⇓nb₂) refl =
    cong₂ pair (quote⇓-det ⇓na₁ ⇓na₂ (fst⇓-det ⇓u₁ ⇓u₂ refl))
               (quote⇓-det ⇓nb₁ ⇓nb₂ (snd⇓-det ⇓v₁ ⇓v₂ refl))
  quote⇓-det (N⇓ ⇓ns₁) (N⇓ ⇓ns₂) refl =
    cong neN (quote*⇓-det ⇓ns₁ ⇓ns₂ refl)
  quote⇓-det zero⇓ zero⇓ refl =
    refl
  quote⇓-det (suc⇓ ⇓n₁) (suc⇓ ⇓n₂) refl =
    cong suc (quote⇓-det ⇓n₁ ⇓n₂ refl)

  quote*⇓-det : ∀ {α Γ} {us₁ us₂ : NeVal Γ α} {ns₁ ns₂}
    (⇓ns₁ : Quote* us₁ ⇓ ns₁) (⇓ns₂ : Quote* us₂ ⇓ ns₂)
    (us₁≡us₂ : us₁ ≡ us₂) →
    ns₁ ≡ ns₂

  quote*⇓-det var⇓ var⇓ refl = refl
  quote*⇓-det (app⇓ ⇓ns₁ ⇓n₁) (app⇓ ⇓ns₂ ⇓n₂) refl =
    cong₂ app (quote*⇓-det ⇓ns₁ ⇓ns₂ refl) (quote⇓-det ⇓n₁ ⇓n₂ refl)
  quote*⇓-det (fst⇓ ⇓ns₁) (fst⇓ ⇓ns₂) refl =
    cong fst (quote*⇓-det ⇓ns₁ ⇓ns₂ refl)
  quote*⇓-det (snd⇓ ⇓ns₁) (snd⇓ ⇓ns₂) refl =
    cong snd (quote*⇓-det ⇓ns₁ ⇓ns₂ refl)
  quote*⇓-det (prim⇓ ⇓nu₁ ⇓nv₁ ⇓ns₁) (prim⇓ ⇓nu₂ ⇓nv₂ ⇓ns₂) refl =
    cong₃ prim (quote⇓-det ⇓nu₁ ⇓nu₂ refl)
               (quote⇓-det ⇓nv₁ ⇓nv₂ refl) (quote*⇓-det ⇓ns₁ ⇓ns₂ refl)

--   Nf t ⇓ n₁ → Nf t ⇓ n₂ → n₁ ≡ n₂

nf⇓-det : ∀ {α Γ} (t : Tm Γ α)
  {n₁} (⇓n₁ : Nf t ⇓ n₁) {n₂} (⇓n₂ : Nf t ⇓ n₂) →
  n₁ ≡ n₂
nf⇓-det t (nf⇓ ⇓u₁ ⇓n₁) (nf⇓ ⇓u₂ ⇓n₂)
  rewrite ⟦⟧⇓-det ⇓u₁ ⇓u₂ refl
  = quote⇓-det ⇓n₁ ⇓n₂ refl
