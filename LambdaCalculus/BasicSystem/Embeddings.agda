module BasicSystem.Embeddings where

open import BasicSystem.Syntax

embˣ : ∀ {Γ α} → Var Γ α → Tm Γ α
embˣ zero = ø
embˣ (suc x) = embˣ x [ ↑ ]

mutual
  emb  : ∀ {Γ α} → Val Γ α → Tm Γ α
  emb (lam t vs) = (ƛ t) [ embˢ vs ]
  emb (ne n)   = embⁿ n 

  embⁿ : ∀ {Γ α} → NeVal Γ α → Tm Γ α
  embⁿ (var x)   = embˣ x 
  embⁿ (app n v) = embⁿ n ∙ emb v
  
  embˢ : ∀ {Γ Σ} → Env Γ Σ → Sub Γ Σ
  embˢ (v ∷ vs) =  emb v ∷ embˢ vs
  embˢ {[]}     [] = ı 
  embˢ {α ∷ Γ} [] = embˢ {Γ} [] ○ ↑

mutual
  nemb  : ∀ {Γ α} → Nf Γ α → Tm Γ α
  nemb (lam n) = ƛ (nemb n) 
  nemb (ne n) = nembⁿ n

  nembⁿ : ∀ {Γ α} → NeNf Γ α → Tm Γ α
  nembⁿ (var x) = embˣ x
  nembⁿ (app n n') = nembⁿ n ∙ nemb n'
