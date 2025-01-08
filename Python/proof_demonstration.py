from typing import List
import math

class InductionProofs:
    """Proofs by Mathematical Induction with Verification"""
    
    @staticmethod
    def sum_first_power(n: int) -> bool:
        """
        Prove sum of first n numbers = n(n+1)/2
        
        Proof:
        1. Base case: n = 1
           LHS = 1
           RHS = 1(1+1)/2 = 1 ✓
        
        2. Inductive step:
           Assume true for k: sum(k) = k(k+1)/2
           Show true for k+1:
           LHS = sum(k) + (k+1)
           = k(k+1)/2 + (k+1)
           = (k^2 + k)/2 + (2k+2)/2
           = (k^2 + 3k + 2)/2
           = (k+1)(k+2)/2
           = RHS ✓
        """
        # Verify formula for given n
        actual_sum = sum(range(1, n + 1))
        formula_sum = (n * (n + 1)) // 2
        return actual_sum == formula_sum
    
    @staticmethod
    def sum_squares(n: int) -> bool:
        """
        Prove sum of first n squares = n(n+1)(2n+1)/6
        
        Proof:
        1. Base case: n = 1
           LHS = 1
           RHS = 1(2)(3)/6 = 1 ✓
        
        2. Inductive step:
           Assume true for k: sum(k^2) = k(k+1)(2k+1)/6
           Show true for k+1:
           LHS = sum(k^2) + (k+1)^2
           = k(k+1)(2k+1)/6 + (k+1)^2
           = [k(k+1)(2k+1) + 6(k+1)^2]/6
           = (k+1)[(2k^2 + k) + 6(k+1)]/6
           = (k+1)(k+2)(2k+3)/6
           = RHS ✓
        """
        actual_sum = sum(i*i for i in range(1, n + 1))
        formula_sum = (n * (n + 1) * (2*n + 1)) // 6
        return actual_sum == formula_sum
    
    @staticmethod
    def sum_cubes(n: int) -> bool:
        """
        Prove sum of first n cubes = [n(n+1)/2]^2
        
        Proof:
        1. Base case: n = 1
           LHS = 1
           RHS = [1(2)/2]^2 = 1 ✓
        
        2. Inductive step:
           Assume true for k: sum(k^3) = [k(k+1)/2]^2
           Show true for k+1:
           LHS = sum(k^3) + (k+1)^3
           = [k(k+1)/2]^2 + (k+1)^3
           = k^2(k+1)^2/4 + (k+1)^3
           = (k+1)^2[k^2/4 + k+1]
           = (k+1)^2[(k+2)^2/4]
           = [(k+1)(k+2)/2]^2
           = RHS ✓
        """
        actual_sum = sum(i*i*i for i in range(1, n + 1))
        formula_sum = (n * (n + 1) // 2) ** 2
        return actual_sum == formula_sum

class InfinitePrimesProof:
    """Proof of Infinite Primes by Contradiction"""
    
    @staticmethod
    def demonstrate_infinite_primes(n: int) -> int:
        """
        Prove there are infinite primes by contradiction
        
        Proof:
        1. Assume there are finitely many primes: p₁, p₂, ..., pₙ
        2. Consider number N = (p₁ × p₂ × ... × pₙ) + 1
        3. N is either prime or composite
        4. If N is prime, we found a prime not in our list
        5. If N is composite, it must have a prime factor
        6. This prime factor cannot be any pᵢ (would leave remainder 1)
        7. Therefore, we found a prime not in our list
        8. Contradiction! ∴ There are infinitely many primes
        
        This function demonstrates by finding a prime not in first n primes
        """
        def is_prime(x: int) -> bool:
            if x < 2:
                return False
            for i in range(2, int(math.sqrt(x)) + 1):
                if x % i == 0:
                    return False
            return True
        
        # Get first n primes
        primes = []
        num = 2
        while len(primes) < n:
            if is_prime(num):
                primes.append(num)
            num += 1
        
        # Construct N = p₁ × p₂ × ... × pₙ + 1
        product = math.prod(primes)
        N = product + 1
        
        # Find smallest prime factor of N
        if is_prime(N):
            return N
        
        for i in range(2, N):
            if N % i == 0 and is_prime(i):
                return i
        
        return N  # Should never reach here

class FermatLittleTheorem:
    """Circular proof demonstration of Fermat's Little Theorem"""
    
    @staticmethod
    def verify_fermat(a: int, p: int) -> bool:
        """
        Verify Fermat's Little Theorem: aᵖ ≡ a (mod p) for prime p
        
        Circular Proof Structure:
        A: aᵖ ≡ a (mod p)
        B: aᵖ⁻¹ ≡ 1 (mod p) for a ≢ 0 (mod p)
        C: p divides aᵖ⁻¹ - 1
        
        Proof:
        A ⟹ B: If aᵖ ≡ a (mod p), then aᵖ⁻¹ ≡ 1 (mod p)
        B ⟹ C: If aᵖ⁻¹ ≡ 1 (mod p), then p|aᵖ⁻¹ - 1
        C ⟹ A: If p|aᵖ⁻¹ - 1, then aᵖ ≡ a (mod p)
        """
        if not is_prime(p):
            return False
        
        # Verify A: aᵖ ≡ a (mod p)
        power_mod = pow(a, p, p)
        a_mod = a % p
        return power_mod == a_mod
    
    @staticmethod
    def demonstrate_circular_proof(a: int, p: int) -> tuple:
        """Demonstrate all three equivalent statements"""
        if a % p == 0:
            return False, False, False
            
        # A: aᵖ ≡ a (mod p)
        A = pow(a, p, p) == a % p
        
        # B: aᵖ⁻¹ ≡ 1 (mod p)
        B = pow(a, p-1, p) == 1
        
        # C: p divides aᵖ⁻¹ - 1
        C = (pow(a, p-1) - 1) % p == 0
        
        return A, B, C

def is_prime(n: int) -> bool:
    """Helper function to check if number is prime"""
    if n < 2:
        return False
    for i in range(2, int(math.sqrt(n)) + 1):
        if n % i == 0:
            return False
    return True

def example_usage():
    """Demonstrate mathematical proofs"""
    
    # Induction Proofs
    n = 5
    print(f"\nVerifying sum formulas for n = {n}:")
    print(f"Sum of first n numbers: {InductionProofs.sum_first_power(n)}")
    print(f"Sum of first n squares: {InductionProofs.sum_squares(n)}")
    print(f"Sum of first n cubes: {InductionProofs.sum_cubes(n)}")
    
    # Infinite Primes
    n = 5
    new_prime = InfinitePrimesProof.demonstrate_infinite_primes(n)
    print(f"\nFound prime ({new_prime}) not in first {n} primes")
    
    # Fermat's Little Theorem
    a, p = 2, 7
    A, B, C = FermatLittleTheorem.demonstrate_circular_proof(a, p)
    print(f"\nFermat's Little Theorem for a={a}, p={p}:")
    print(f"A: aᵖ ≡ a (mod p): {A}")
    print(f"B: aᵖ⁻¹ ≡ 1 (mod p): {B}")
    print(f"C: p divides aᵖ⁻¹ - 1: {C}")

if __name__ == "__main__":
    example_usage()
