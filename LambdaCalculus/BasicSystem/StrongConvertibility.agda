module BasicSystem.StrongConvertibility where

open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.OPE
open import BasicSystem.OPELemmas
open import BasicSystem.RecursiveNormaliser
open import BasicSystem.OPERecursive

_∼_ : ∀ {Γ α} → Val Γ α → Val Γ α → Set 
_∼_ {Γ}{⋆}     (ne n) (ne n') = quotⁿ n ≡ quotⁿ n'   
_∼_ {Γ}{α ⇒ β} v       v'       = ∀ {B}(f : OPE B Γ){a a' : Val B α} → 
    a ∼ a' → (vmap f v ∙∙ a) ∼ (vmap f v' ∙∙ a')

data _∼ˢ_ {Γ : Ctx} : ∀ {Δ} → Env Γ Δ → Env Γ Δ → Set where
  ∼[]  : [] ∼ˢ []
  ∼<< : ∀ {Δ α}{vs vs' : Env Γ Δ}{v v' : Val Γ α} → 
        vs ∼ˢ vs' → v ∼ v' → (v ∷ vs) ∼ˢ (v' ∷ vs')

helper : ∀ {Θ}{α}{β}{f f' f'' f''' : Val Θ (α ⇒ β)} → 
         f ≡ f' → f'' ≡ f''' → {a a' : Val Θ α} → 
         (f' ∙∙ a) ∼ (f''' ∙∙ a') → (f ∙∙ a) ∼ (f'' ∙∙ a')
helper refl refl p = p 

helper' : ∀ {Γ Δ α β}{t : Tm (α ∷ Δ) β}{vs vs' vs'' : Env Γ Δ} → 
          vs'' ≡ vs' → {a a' : Val Γ α} →          
          eval t (a ∷ vs) ∼ eval t (a' ∷ vs') → 
          eval t (a ∷ vs) ∼ eval t (a' ∷ vs'')
helper' refl p = p 

∼map : ∀ {Γ Δ α}(f : OPE Γ Δ){v v' : Val Δ α} → v ∼ v' →
       vmap f v ∼ vmap f v'
∼map {α = ⋆}     f {ne n}{ne n'}  p = 
  trans (qⁿmaplem f n) (trans (cong (nenmap f) p) (sym (qⁿmaplem f n')) ) 
∼map {α = α ⇒ β} f {v}    {v'}      p = λ f' p' → 
   helper (compvmap f' f v) (compvmap f' f v') (p (comp f' f) p')  

∼ˢmap : ∀ {B Γ Δ}(f : OPE B Γ){vs vs' : Env Γ Δ} → vs ∼ˢ vs' → 
        emap f vs ∼ˢ emap f vs'
∼ˢmap f ∼[]         = ∼[] 
∼ˢmap f (∼<< p p') = ∼<< (∼ˢmap f p) (∼map f p') 

mutual
  sym∼ : ∀ {Γ α}{v v' : Val Γ α} → v ∼ v' → v' ∼ v
  sym∼ {α = ⋆}     {ne n}{ne n'} p = sym p 
  sym∼ {α = α ⇒ β}                 p = λ f p' → sym∼ (p f (sym∼ p'))   


  sym∼ˢ : ∀ {Γ Δ}{vs vs' : Env Γ Δ} → vs ∼ˢ vs' → vs' ∼ˢ vs
  sym∼ˢ ∼[]        = ∼[] 
  sym∼ˢ (∼<< p q) = ∼<< (sym∼ˢ p) (sym∼ q)

mutual
  trans∼ : ∀ {Γ α}{v v' v'' : Val Γ α} → v ∼ v' → v' ∼ v'' → v ∼ v''
  trans∼ {α = ⋆}     {ne n}{ne n'}{ne n''} p p' = trans p p' 
  trans∼ {α = α ⇒ β}                          p p' = λ f p'' → 
    trans∼ (p f (trans∼ p'' (sym∼ p''))) (p' f p'')  

  -- using that if a is related to a' then a is related to a

  trans∼ˢ : ∀ {Γ Δ}{vs vs' vs'' : Env Γ Δ} → 
            vs ∼ˢ vs' → vs' ∼ˢ vs'' → vs ∼ˢ vs''
  trans∼ˢ ∼[]         ∼[]         = ∼[] 
  trans∼ˢ (∼<< p p') (∼<< q q') = ∼<< (trans∼ˢ p q) (trans∼ p' q')
