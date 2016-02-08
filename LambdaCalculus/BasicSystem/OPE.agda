module BasicSystem.OPE where

open import BasicSystem.Syntax

data OPE : Ctx → Ctx → Set where
  done : OPE [] []
  keep : ∀ {Γ Δ} α → OPE Γ Δ → OPE (α ∷ Γ) (α ∷ Δ)
  skip : ∀ {Γ Δ} α → OPE Γ Δ → OPE (α ∷ Γ) Δ

oid : ∀ {Γ} → OPE Γ Γ
oid {[]}     = done
oid {α ∷ Γ} = keep α oid

comp : ∀ {B Γ Δ} → OPE B Γ → OPE Γ Δ → OPE B Δ
comp done     done          = done
comp (skip α f) g           = skip α (comp f g) 
comp (keep α f) (keep .α g) = keep α (comp f g) 
comp (keep α f) (skip .α g) = skip α (comp f g)

weak : ∀ {Γ} β → OPE (β ∷ Γ) Γ
weak β = skip β oid

-- Variables
xmap : ∀ {Γ Δ α} → OPE Γ Δ → Var Δ α → Var Γ α
xmap done     ()
xmap (keep α f) zero        = zero
xmap (keep α f) (suc x) = suc (xmap f x)
xmap (skip α f) x         = suc (xmap f x)

-- Values
mutual
  vmap : ∀ {Γ Δ α} → OPE Γ Δ → Val Δ α → Val Γ α
  vmap f (lam t vs) = lam t (emap f vs) 
  vmap f (ne n)   = ne (nevmap f n) 

  nevmap : ∀ {Γ Δ α} → OPE Γ Δ → NeVal Δ α → NeVal Γ α
  nevmap f (var x)   = var (xmap f x)  
  nevmap f (app n v) = app (nevmap f n) (vmap f v) 

  emap : ∀ {B Γ Δ} → OPE B Γ → Env Γ Δ → Env B Δ
  emap f []         = [] 
  emap f (v ∷ vs) = vmap f v ∷ emap f vs 

-- weakening for values
vwk : ∀ {Γ α} β → Val Γ α → Val (β ∷ Γ) α
vwk β v = vmap (weak β) v

-- Normal forms
mutual
  nfmap : ∀ {Γ Δ α} → OPE Γ Δ → Nf Δ α → Nf Γ α
  nfmap f (lam n) = lam (nfmap (keep _ f) n) 
  nfmap f (ne n) = ne (nenmap f n) 

  nenmap : ∀ {Γ Δ α} → OPE Γ Δ → NeNf Δ α → NeNf Γ α
  nenmap f (var x)    = var (xmap f x) 
  nenmap f (app n n') = app (nenmap f n) (nfmap f n')

-- Embedding
oemb : ∀ {Γ Δ} → OPE Γ Δ → Sub Γ Δ
oemb done       = ı 
oemb (keep α f) =  ø ∷ (oemb f ○ ↑)
oemb (skip α f) = oemb f ○ ↑
