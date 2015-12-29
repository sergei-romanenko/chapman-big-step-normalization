module BasicSystem.Embeddings where

open import BasicSystem.Syntax

embˣ : ∀ {Γ σ} → Var Γ σ → Tm Γ σ
embˣ vZ       = top 
embˣ (vS τ x) = embˣ x [ pop τ ]

mutual
  emb  : ∀ {Γ σ} → Val Γ σ → Tm Γ σ
  emb (λv t vs) = λt t [ embˢ vs ] 
  emb (nev n)   = embⁿ n 

  embⁿ : ∀ {Γ σ} → NeV Γ σ → Tm Γ σ
  embⁿ (varV x)   = embˣ x 
  embⁿ (appV n v) = embⁿ n $ emb v
  
  embˢ : ∀ {Γ Σ} → Env Γ Σ → Sub Γ Σ
  embˢ (vs << v) = embˢ vs < emb v
  embˢ {ε}     ε = id 
  embˢ {Γ < σ} ε = embˢ {Γ} ε ○ pop σ 

mutual
  nemb  : ∀ {Γ σ} → Nf Γ σ → Tm Γ σ
  nemb (λn n) = λt (nemb n) 
  nemb (ne n) = nembⁿ n

  nembⁿ : ∀ {Γ σ} → NeN Γ σ → Tm Γ σ
  nembⁿ (varN x) = embˣ x
  nembⁿ (appN n n') = nembⁿ n $ nemb n'