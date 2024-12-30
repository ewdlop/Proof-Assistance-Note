-- Import necessary libraries
import data.nat.basic

-- Define what it means for a number to be even
def is_even (n : ℕ) : Prop := ∃ k, n = 2 * k

-- Theorem: Sum of two even numbers is even
theorem sum_of_evens (a b : ℕ) (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
begin
  -- Unpack the hypotheses to get the definitions of a and b being even
  cases h1 with k1 hk1,
  cases h2 with k2 hk2,
  -- Use the definitions to rewrite a and b
  rw hk1,
  rw hk2,
  -- Show that a + b is even
  use (k1 + k2),
  -- Simplify the expression
  ring,
end
