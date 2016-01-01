module FiniteProducts.StrongConvertibility where
open import FiniteProducts.Syntax
open import FiniteProducts.OPE
open import FiniteProducts.OPELemmas
open import FiniteProducts.OPERecursive
open import FiniteProducts.RecursiveNormaliser
open import FiniteProducts.Utils

_∼_ : ∀ {Γ σ} → Val Γ σ → Val Γ σ → Set 
_∼_ {Γ}{ι}     (nev n) (nev n') = quotⁿ n ≡ quotⁿ n'   
_∼_ {Γ}{σ ⇒ τ} v       v'       = ∀ {B}(f : OPE B Γ){a a' : Val B σ} → 
    a ∼ a' → (vmap f v $$ a) ∼ (vmap f v' $$ a')
_∼_ {Γ}{One}   v       v'       = True
_∼_ {Γ}{σ * τ} v       v'       = (vfst v ∼ vfst v') × (vsnd v ∼ vsnd v') 

data _∼ˢ_ {Γ : Con} : ∀ {Δ} → Env Γ Δ → Env Γ Δ → Set where
  ∼ε  : ε ∼ˢ ε
  ∼<< : ∀ {Δ σ}{vs vs' : Env Γ Δ}{v v' : Val Γ σ} → 
        vs ∼ˢ vs' → v ∼ v' → (vs << v) ∼ˢ (vs' << v')

helper : ∀ {Θ}{σ}{τ}{f f' f'' f''' : Val Θ (σ ⇒ τ)} → 
         f ≡ f' → f'' ≡ f''' → {a a' : Val Θ σ} → 
         (f' $$ a) ∼ (f''' $$ a') → (f $$ a) ∼ (f'' $$ a')
helper refl refl p = p 

helper' : ∀ {Γ Δ σ τ}{t : Tm (Δ < σ) τ}{vs vs' vs'' : Env Γ Δ} → 
          vs'' ≡ vs' → {a a' : Val Γ σ} →          
          eval t (vs << a) ∼ eval t (vs' << a') → 
          eval t (vs << a) ∼ eval t (vs'' << a')
helper' refl p = p 

∼map : ∀ {Γ Δ σ}(f : OPE Γ Δ){v v' : Val Δ σ} → v ∼ v' →
       vmap f v ∼ vmap f v'
∼map {σ = ι}     f {nev n}{nev n'}  p        = 
  trans (qⁿmaplem f n) (trans (cong (nenmap f) p) (sym (qⁿmaplem f n')) ) 
∼map {σ = σ ⇒ τ} f {v}    {v'}      p        = λ f' p' → 
   helper (compvmap f' f v) (compvmap f' f v') (p (comp f' f) p')  
∼map {σ = One}   f {v}    {v'}      p        = void 
∼map {σ = σ * τ} f {v}    {v'}      (p , q) with ∼map f p | ∼map f q
... | p' | q' with vmap f (vfst v) | vmap f (vfst v') | vfstmaplem f v | vfstmaplem f v' | vmap f (vsnd v) | vmap f (vsnd v') | vsndmaplem f v | vsndmaplem f v'
... | ._ | ._ | refl | refl | ._ | ._ | refl | refl = p' , q'  

∼ˢmap : ∀ {B Γ Δ}(f : OPE B Γ){vs vs' : Env Γ Δ} → vs ∼ˢ vs' → 
        emap f vs ∼ˢ emap f vs'
∼ˢmap f ∼ε         = ∼ε 
∼ˢmap f (∼<< p p') = ∼<< (∼ˢmap f p) (∼map f p') 

mutual
  sym∼ : ∀ {Γ σ}{v v' : Val Γ σ} → v ∼ v' → v' ∼ v
  sym∼ {σ = ι}     {nev n}{nev n'} p        = sym p 
  sym∼ {σ = σ ⇒ τ}                 p        = λ f p' → sym∼ (p f (sym∼ p'))   
  sym∼ {σ = One}                   p        = void 
  sym∼ {σ = σ * τ}                 (p , q) = sym∼ p , sym∼ q 

  sym∼ˢ : ∀ {Γ Δ}{vs vs' : Env Γ Δ} → vs ∼ˢ vs' → vs' ∼ˢ vs
  sym∼ˢ ∼ε        = ∼ε 
  sym∼ˢ (∼<< p q) = ∼<< (sym∼ˢ p) (sym∼ q)

mutual
  trans∼ : ∀ {Γ σ}{v v' v'' : Val Γ σ} → v ∼ v' → v' ∼ v'' → v ∼ v''
  trans∼ {σ = ι}     {nev n}{nev n'}{nev n''} p p' = trans p p' 
  trans∼ {σ = σ ⇒ τ}                          p p' = λ f p'' → 
    trans∼ (p f (trans∼ p'' (sym∼ p''))) (p' f p'')  
  trans∼ {σ = One}                            p p' = void 
  trans∼ {σ = σ * τ}                          (p , p') (q , q') = 
    trans∼ p q , trans∼ p' q' 

  -- using that if a is related to a' then a is related to a

  trans∼ˢ : ∀ {Γ Δ}{vs vs' vs'' : Env Γ Δ} → 
            vs ∼ˢ vs' → vs' ∼ˢ vs'' → vs ∼ˢ vs''
  trans∼ˢ ∼ε         ∼ε         = ∼ε 
  trans∼ˢ (∼<< p p') (∼<< q q') = ∼<< (trans∼ˢ p q) (trans∼ p' q')
