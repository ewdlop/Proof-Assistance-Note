from typing import List, Tuple, Optional, Dict, Set
from dataclasses import dataclass
from enum import Enum
import math

class ProofDirection(Enum):
    FORWARD = "forward"
    BACKWARD = "backward"

@dataclass
class Statement:
    """Mathematical statement with truth value"""
    content: str
    implies: List['Statement'] = None
    implied_by: List['Statement'] = None
    truth_value: Optional[bool] = None

    def __post_init__(self):
        if self.implies is None:
            self.implies = []
        if self.implied_by is None:
            self.implied_by = []

class BackwardProof:
    """Implementation of backward law proofs"""
    
    def __init__(self):
        self.statements: Dict[str, Statement] = {}
        self.goal: Optional[Statement] = None
    
    def add_statement(self, content: str, truth_value: Optional[bool] = None) -> None:
        """Add statement to proof system"""
        if content not in self.statements:
            self.statements[content] = Statement(content, truth_value=truth_value)
    
    def add_implication(self, p: str, q: str) -> None:
        """Add implication p => q"""
        if p not in self.statements:
            self.add_statement(p)
        if q not in self.statements:
            self.add_statement(q)
            
        self.statements[p].implies.append(self.statements[q])
        self.statements[q].implied_by.append(self.statements[p])
    
    def set_goal(self, content: str) -> None:
        """Set goal statement to prove"""
        if content not in self.statements:
            self.add_statement(content)
        self.goal = self.statements[content]
    
    def backward_chain(self) -> List[List[Statement]]:
        """
        Find all possible backward chains to prove goal
        Returns list of proof paths
        """
        if not self.goal:
            return []
            
        paths = []
        visited = set()
        
        def dfs(statement: Statement, path: List[Statement]) -> None:
            """Depth-first search for proof paths"""
            if statement.truth_value is True:
                paths.append(path[:])
                return
                
            if statement in visited:
                return
                
            visited.add(statement)
            for premise in statement.implied_by:
                path.append(premise)
                dfs(premise, path)
                path.pop()
            visited.remove(statement)
        
        dfs(self.goal, [self.goal])
        return paths

class ReverseTheoremProver:
    """Prove theorems using backward reasoning"""
    
    @staticmethod
    def prove_reverse_triangle_inequality() -> BackwardProof:
        """
        Prove: |a + b| ≥ ||a| - |b||
        Using backward reasoning
        """
        proof = BackwardProof()
        
        # Add statements
        proof.add_statement("|a + b| ≥ ||a| - |b||")  # Goal
        proof.add_statement("|a + b|² ≥ (|a| - |b|)²")
        proof.add_statement("(a + b)(a + b) ≥ (|a| - |b|)(|a| - |b|)")
        proof.add_statement("a² + 2ab + b² ≥ |a|² - 2|a||b| + |b|²")
        proof.add_statement("2ab ≥ -2|a||b|")
        proof.add_statement("ab ≥ -|a||b|")  # True for all a, b
        
        # Add implications (backward)
        proof.add_implication("ab ≥ -|a||b|", "2ab ≥ -2|a||b|")
        proof.add_implication("2ab ≥ -2|a||b|", "a² + 2ab + b² ≥ |a|² - 2|a||b| + |b|²")
        proof.add_implication("a² + 2ab + b² ≥ |a|² - 2|a||b| + |b|²", "(a + b)(a + b) ≥ (|a| - |b|)(|a| - |b|)")
        proof.add_implication("(a + b)(a + b) ≥ (|a| - |b|)(|a| - |b|)", "|a + b|² ≥ (|a| - |b|)²")
        proof.add_implication("|a + b|² ≥ (|a| - |b|)²", "|a + b| ≥ ||a| - |b||")
        
        # Set goal
        proof.set_goal("|a + b| ≥ ||a| - |b||")
        
        return proof
    
    @staticmethod
    def prove_cauchy_schwarz() -> BackwardProof:
        """
        Prove Cauchy-Schwarz inequality backward:
        |⟨x,y⟩| ≤ ||x|| ||y||
        """
        proof = BackwardProof()
        
        # Add statements
        proof.add_statement("|⟨x,y⟩| ≤ ||x|| ||y||")  # Goal
        proof.add_statement("|⟨x,y⟩|² ≤ ||x||² ||y||²")
        proof.add_statement("⟨x,y⟩⟨x,y⟩ ≤ ⟨x,x⟩⟨y,y⟩")
        proof.add_statement("||αx + βy||² ≥ 0 for all α,β")  # True by inner product properties
        
        # Add implications (backward)
        proof.add_implication("||αx + βy||² ≥ 0 for all α,β", "⟨x,y⟩⟨x,y⟩ ≤ ⟨x,x⟩⟨y,y⟩")
        proof.add_implication("⟨x,y⟩⟨x,y⟩ ≤ ⟨x,x⟩⟨y,y⟩", "|⟨x,y⟩|² ≤ ||x||² ||y||²")
        proof.add_implication("|⟨x,y⟩|² ≤ ||x||² ||y||²", "|⟨x,y⟩| ≤ ||x|| ||y||")
        
        # Set goal
        proof.set_goal("|⟨x,y⟩| ≤ ||x|| ||y||")
        
        return proof
    
    @staticmethod
    def prove_am_gm() -> BackwardProof:
        """
        Prove AM-GM inequality backward:
        (x₁ + ... + xₙ)/n ≥ (x₁...xₙ)^(1/n)
        """
        proof = BackwardProof()
        
        # Add statements
        proof.add_statement("(x₁ + ... + xₙ)/n ≥ (x₁...xₙ)^(1/n)")  # Goal
        proof.add_statement("ln((x₁ + ... + xₙ)/n) ≥ ln((x₁...xₙ)^(1/n))")
        proof.add_statement("ln((x₁ + ... + xₙ)/n) ≥ (ln(x₁) + ... + ln(xₙ))/n")
        proof.add_statement("Jensen's inequality for ln (concave)")  # True
        
        # Add implications (backward)
        proof.add_implication("Jensen's inequality for ln (concave)",
                            "ln((x₁ + ... + xₙ)/n) ≥ (ln(x₁) + ... + ln(xₙ))/n")
        proof.add_implication("ln((x₁ + ... + xₙ)/n) ≥ (ln(x₁) + ... + ln(xₙ))/n",
                            "ln((x₁ + ... + xₙ)/n) ≥ ln((x₁...xₙ)^(1/n))")
        proof.add_implication("ln((x₁ + ... + xₙ)/n) ≥ ln((x₁...xₙ)^(1/n))",
                            "(x₁ + ... + xₙ)/n ≥ (x₁...xₙ)^(1/n)")
        
        # Set goal
        proof.set_goal("(x₁ + ... + xₙ)/n ≥ (x₁...xₙ)^(1/n)")
        
        return proof

def example_usage():
    """Demonstrate backward law proofs"""
    
    # Example 1: Reverse Triangle Inequality
    print("\nProving Reverse Triangle Inequality:")
    rti_proof = ReverseTheoremProver.prove_reverse_triangle_inequality()
    paths = rti_proof.backward_chain()
    
    print("Proof Path:")
    for path in paths:
        print("\nPath:")
        for statement in reversed(path):  # Print in forward order
            print(f"=> {statement.content}")
    
    # Example 2: Cauchy-Schwarz Inequality
    print("\nProving Cauchy-Schwarz Inequality:")
    cs_proof = ReverseTheoremProver.prove_cauchy_schwarz()
    paths = cs_proof.backward_chain()
    
    print("Proof Path:")
    for path in paths:
        print("\nPath:")
        for statement in reversed(path):
            print(f"=> {statement.content}")
    
    # Example 3: AM-GM Inequality
    print("\nProving AM-GM Inequality:")
    amgm_proof = ReverseTheoremProver.prove_am_gm()
    paths = amgm_proof.backward_chain()
    
    print("Proof Path:")
    for path in paths:
        print("\nPath:")
        for statement in reversed(path):
            print(f"=> {statement.content}")

if __name__ == "__main__":
    example_usage()
