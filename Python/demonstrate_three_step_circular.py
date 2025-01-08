from enum import Enum
from typing import List, Dict, Set, Tuple
from dataclasses import dataclass

class TruthValue(Enum):
    TRUE = True
    FALSE = False
    UNDETERMINED = None

@dataclass
class Proposition:
    """A logical proposition with its truth value"""
    symbol: str
    value: TruthValue = TruthValue.UNDETERMINED
    negation: bool = False
    
    def __str__(self) -> str:
        return f"~{self.symbol}" if self.negation else self.symbol
    
    def negate(self) -> 'Proposition':
        """Return negation of this proposition"""
        return Proposition(self.symbol, self.value, not self.negation)

class CircularImplication:
    """Analysis of p=>~p=>p type circular implications"""
    
    def __init__(self):
        self.implications: List[Tuple[Proposition, Proposition]] = []
    
    def add_implication(self, p: Proposition, q: Proposition) -> None:
        """Add implication p => q"""
        self.implications.append((p, q))
    
    def setup_three_step(self, p: str) -> None:
        """Setup p=>~p=>p chain"""
        prop_p = Proposition(p)
        prop_not_p = prop_p.negate()
        
        # p => ~p
        self.add_implication(prop_p, prop_not_p)
        # ~p => p
        self.add_implication(prop_not_p, prop_p)
    
    def analyze_truth_values(self) -> Dict[str, List[TruthValue]]:
        """
        Analyze possible truth value combinations
        
        For p=>~p=>p:
        1. If p is True:
           - Then ~p must be True (from p=>~p)
           - But if ~p is True, p must be False
           - Contradiction!
        
        2. If p is False:
           - Then ~p is True
           - Then p must be True (from ~p=>p)
           - Contradiction!
        """
        results = {}
        propositions = set()
        
        # Collect all unique propositions
        for p, q in self.implications:
            propositions.add(p.symbol)
            propositions.add(q.symbol)
        
        # Try all possible truth value combinations
        for prop in propositions:
            possible_values = []
            
            # Try setting p to True
            implication_valid = True
            current_values = {prop: TruthValue.TRUE}
            
            for p, q in self.implications:
                if p.symbol in current_values:
                    p_value = current_values[p.symbol]
                    if p.negation:
                        p_value = TruthValue.TRUE if p_value == TruthValue.FALSE else TruthValue.FALSE
                        
                    # Determine implied value for q
                    q_value = TruthValue.TRUE
                    if q.negation:
                        q_value = TruthValue.FALSE
                        
                    if q.symbol in current_values and current_values[q.symbol] != q_value:
                        implication_valid = False
                        break
                        
                    current_values[q.symbol] = q_value
            
            if implication_valid:
                possible_values.append(TruthValue.TRUE)
            
            # Try setting p to False
            implication_valid = True
            current_values = {prop: TruthValue.FALSE}
            
            for p, q in self.implications:
                if p.symbol in current_values:
                    p_value = current_values[p.symbol]
                    if p.negation:
                        p_value = TruthValue.TRUE if p_value == TruthValue.FALSE else TruthValue.FALSE
                        
                    # Determine implied value for q
                    q_value = TruthValue.TRUE
                    if q.negation:
                        q_value = TruthValue.FALSE
                        
                    if q.symbol in current_values and current_values[q.symbol] != q_value:
                        implication_valid = False
                        break
                        
                    current_values[q.symbol] = q_value
            
            if implication_valid:
                possible_values.append(TruthValue.FALSE)
            
            results[prop] = possible_values
        
        return results

class ImplicationChain:
    """Analysis of implication chains and cycles"""
    
    def __init__(self):
        self.implications: Dict[str, Set[str]] = {}
    
    def add_implication(self, p: str, q: str) -> None:
        """Add implication p => q"""
        if p not in self.implications:
            self.implications[p] = set()
        self.implications[p].add(q)
    
    def find_cycles(self) -> List[List[str]]:
        """Find all implication cycles"""
        cycles = []
        visited = set()
        path = []
        
        def dfs(node: str) -> None:
            """Depth-first search for cycles"""
            path.append(node)
            visited.add(node)
            
            if node in self.implications:
                for next_node in self.implications[node]:
                    if next_node not in visited:
                        dfs(next_node)
                    elif next_node in path:
                        # Found cycle
                        cycle_start = path.index(next_node)
                        cycles.append(path[cycle_start:])
            
            path.pop()
            visited.remove(node)
        
        # Start DFS from each node
        for node in self.implications:
            if node not in visited:
                dfs(node)
        
        return cycles

def demonstrate_three_step_circular():
    """Demonstrate p=>~p=>p chain analysis"""
    
    print("\nAnalyzing p=>~p=>p:")
    print("====================")
    
    # Setup implication chain
    circular = CircularImplication()
    circular.setup_three_step("p")
    
    # Analyze possible truth values
    results = circular.analyze_truth_values()
    
    print("\nPossible truth values for propositions:")
    for prop, values in results.items():
        if not values:
            print(f"{prop}: No consistent truth values possible")
        else:
            value_str = ", ".join(str(v.value) for v in values)
            print(f"{prop}: {value_str}")
    
    # Find implications cycles
    chain = ImplicationChain()
    chain.add_implication("p", "~p")
    chain.add_implication("~p", "p")
    
    cycles = chain.find_cycles()
    
    print("\nImplication cycles found:")
    for cycle in cycles:
        print(" => ".join(cycle))
    
    print("\nLogical Analysis:")
    print("1. If p is True:")
    print("   - Then ~p must be True (from p=>~p)")
    print("   - If ~p is True, then p must be True (from ~p=>p)")
    print("   - Both p and ~p are True: Contradiction!")
    print("\n2. If p is False:")
    print("   - Then ~p is True")
    print("   - If ~p is True, then p must be True (from ~p=>p)")
    print("   - Contradiction!")
    print("\nConclusion:")
    print("The system p=>~p=>p is inconsistent")
    print("It cannot have a consistent truth assignment")

if __name__ == "__main__":
    demonstrate_three_step_circular()
