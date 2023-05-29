import data.real.basic
import data.nat.choose.sum
import algebra.big_operators.basic
import topology.subset_properties -- Compacité (fermés bornés de ℝ)
import topology.metric_space.basic -- Distance
-- import order.liminf_limsup -- Supremum NOPE

-- import defs -- is_fbounded
import main -- Bolzano-Weierstrass

open_locale big_operators -- Notation ∑ 
open finset
open set

noncomputable theory


-- DEFINITION polynôme de Bernstein.
definition coeff_binom : ℕ → ℕ → ℕ
  | _             0 := 1
  | 0       (k + 1) := 0
  | (n + 1) (k + 1) := coeff_binom n k + coeff_binom n (k + 1)


definition bernstein_coeff (k : ℕ) (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :=
  f ( k / n ) * coeff_binom n k * (x)^k * (1 - x)^(n - k)

definition bernstein_poly (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :=
  ∑ k in range n, bernstein_coeff k n f x


-- LEMME 2.
def f₁ (x : ℝ) : ℝ := 1
def f₂ (x : ℝ) : ℝ := x
def f₃ (x : ℝ) : ℝ := x^2
def f₄ (j : ℕ) (x : ℝ) : ℝ := (x - j)^2

lemma B_1f (n : ℕ) (x : ℝ) : bernstein_poly n f₁ x = 1 :=
begin
  let res := add_pow 1 0 n,
--  have h₁ : res = 1 := 
  sorry,
end

lemma B_2f (n : ℕ) (x : ℝ): bernstein_poly n f₂ x = x :=
begin
  sorry,
end

lemma B_3f (n : ℕ) (x : ℝ): bernstein_poly n f₃ x = ((n - 1) * x^2 + x) / n :=
begin
  sorry,
end

lemma sum_xkn (n : ℕ) (k : finset.range n) (x : ℝ) : bernstein_poly n (f₄ k / n) x = x * (1 - x) / n := -- putain de k
begin
  sorry,
end

-- NORME SUP
definition is_upper_bound (S : set ℝ) (x : ℝ) := 
  ∀ s ∈ S, s ≤ x 

definition is_least_upper_bound (S : set ℝ) (x : ℝ) := 
  is_upper_bound S x ∧ ∀ y : ℝ, is_upper_bound S y → x ≤ y

definition has_least_upper_bound (S : set ℝ) := 
  ∃ x, is_least_upper_bound S x 

--noncomputable instance : has_dist ℝ := 
--  { λ f g, Sup |f x - g x | des trucs } } 
-- { dist := λ f g, Sup { |f x - g x| | x ∈ ℝ } } -- SUP


-- régler le has_dist !!!!

-- CONTINUITÉ (UNIFORME) SUR UN INTERVAL.
definition is_continuous {I : set ℝ} (f : I → ℝ) := 
  ∀ (x : I), ∀ (ε : ℝ), ε > 0 → 
    ∃ (η : ℝ) (h₀ : η > 0), 
      ∀ (y : I), has_dist.dist x y ≤ η → has_dist.dist (f x) (f y) ≤ ε

definition is_ucontinuous {I : set ℝ} (f : I → ℝ) :=
  ∀ (ε : ℝ), ε > 0 → 
    ∃ (η : ℝ) (h₀ : η > 0), 
      ∀ (x : I), ∀ (y : I), has_dist.dist x y ≤ η → has_dist.dist (f x) (f y) ≤ ε


-- LIMITE (usuelle et uniforme)
definition is_limit (a : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ (ε : ℝ), ε > 0 → 
    ∃ (N : ℕ), ∀ n ≥ N, has_dist.dist (a n) l ≤ ε

-- LIMITE DE FONCTION

-- CONVERGENCE (simple et uniforme)
definition s_convergence {I : set ℝ} (fn : ℕ → (I → ℝ)) (f : I → ℝ) :=
  ∀ (x : I), ∀ (ε : ℝ), ε > 0 →
    ∃ (N : ℕ), ∀ n ≥ N, has_dist.dist (fn n x) (f x) ≤ ε 

--definition u_convergence {I : set ℝ} (fn : ℕ → (I → ℝ)) (f : I → ℝ) :=
  -- existe un rang à partir duquel différence est bornée
 -- ∃ (N : ℕ), basic_real_analysis.is_fbounded I (fn N - f)
--  ∃ M, ∀ x, ∃ N, | fn N - f | ≤ M ∧ 
  -- MERDE

-- THÉORÈMES NÉCESSAIRES À LA DÉMONSTRATION DE WEIERSTRASS
theorem extreme_value (I : set ℝ) (hcp : is_compact I)
                      (f : I → ℝ) (hct : is_continuous f) : 
                        ∃ M > 0, (∀ x, f x ≤ M) ∧ (∃ x₀, f x₀ = M) :=
begin
  -- https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_des_valeurs_extr%C3%AAmes#D%C3%A9monstration_sans_les_th%C3%A9or%C3%A8mes_topologiques

  -- On prouve l'existence de la borne supérieure M.
  sorry,
end

theorem heine (I : set ℝ) (hcp : is_compact I) 
              (f : I → ℝ) (hct : is_continuous f) : is_ucontinuous f =
begin
  sorry, 
end

-- THÉORÈME DE WEIERSTRASS.
theorem weierstrass (I : set ℝ) (hcp : is_compact I)  
                    (f : I → ℝ) (hct : is_continuous f) 
                    (Bnf : I → I) : :=
begin 
  sorry,
end
