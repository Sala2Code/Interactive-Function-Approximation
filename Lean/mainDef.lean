import data.real.basic

namespace basic_real_analysis
-- * Continuité * --
def is_continuous_at (f : ℝ → ℝ) (x₀ : ℝ) := 
  ∀ x, ∀ ε > 0, ∃ η > 0, |x - x₀| ≤  η → |f x - f x₀| ≤ ε

def is_ucontinuous (f : ℝ → ℝ) := 
  ∀ ε > 0, ∃ η > 0, ∀ x y, |x - y| ≤ η → |f x - f y| ≤ ε

def is_lipschitzienne (f : ℝ → ℝ) := 
  ∃ k > 0, ∀ x y, |f x - f y| ≤ k * |x - y|

-- * Convergence * --

def u_converge (u : ℕ → ℝ) := 
  ∃ l, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |u n - l| ≤ ε

-- * Fonction * --
def int_ferme (a b : ℝ ) : set ℝ := 
  {x : ℝ | a ≤ x ∧ x ≤ b}


def is_fbounded (A : set ℝ) (f : A → set ℝ) := 
  ∃ M, ∀ x, |f x| ≤ M

def is_ubounded (u : ℕ → ℝ) :=
  ∃ M>0, ∀ n, abs(u n) ≤ M


-- * Suites * --
def is_monotone_real (u : ℕ → ℝ) := 
  ∀ n, u (n+1) ≥ u n ∨ u (n+1) ≤ u n

def is_strict_increasing_nat (u : ℕ → ℕ )  :=
  ∀ n : ℕ, u (n+1) > u n 

def is_strict_increasing_real (u : ℕ → ℝ )  :=
  ∀ n : ℕ, u (n+1) > u n 

def is_subsequence_of (u : ℕ → ℝ ) (v : ℕ → ℝ ) := 
  ∃ φ : ℕ → ℕ, is_strict_increasing_nat φ ∧ ∀ n, u n = v (φ n)

def is_cauchy (u : ℕ → ℝ ) :=
  ∀ ε > 0, ∃ N : ℕ, ∀ p q : ℕ, p ≥ N ∧ q ≥ N → |u p - u q| ≤ ε

-- Pour un lemme
def is_peak (n : ℕ) (u : ℕ → ℝ) := 
  ∀ k, k ≥ n → u k < u n

end basic_real_analysis
