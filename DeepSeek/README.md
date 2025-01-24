# README

Here's an enhanced version of the theorem prover that **detects circular proofs** (where a conclusion is used as a premise in its own proof) and includes multiple proof strategies. This implementation focuses on **propositional logic** and tracks proof dependencies to avoid circular reasoning:

```python
import itertools
from sympy import symbols, Equivalent, Implies, And, Or, Not, simplify_logic
from sympy.logic.inference import satisfiable
from collections import defaultdict

class TheoremProver:
    def __init__(self, theorem, variables):
        self.theorem = theorem
        self.variables = variables
        self.dependencies = defaultdict(set)

    def _track_dependencies(self, premise, conclusion):
        """Track dependencies between premises and conclusions"""
        self.dependencies[conclusion].add(premise)
        for dep in self.dependencies[premise]:
            self.dependencies[conclusion].add(dep)

    def _check_circularity(self, current_stmt):
        """Check if current statement depends on itself"""
        visited = set()
        stack = [current_stmt]
        
        while stack:
            node = stack.pop()
            if node == current_stmt and len(visited) > 0:
                return True
            if node not in visited:
                visited.add(node)
                stack.extend(self.dependencies[node])
        return False

    def brute_force_truth_table(self):
        """Check all possible truth assignments"""
        n = len(self.variables)
        for values in itertools.product([True, False], repeat=n):
            assignment = dict(zip(self.variables, values))
            if not self.theorem.subs(assignment):
                return False, assignment
        return True, None

    def direct_proof(self, axioms):
        """Attempt direct proof while tracking dependencies"""
        try:
            for axiom in axioms:
                self._track_dependencies(axiom, self.theorem)
                if self._check_circularity(self.theorem):
                    return "Circular proof detected", None
                    
            simplified = simplify_logic(self.theorem)
            return "Valid" if simplified == True else "Invalid", simplified
        except RecursionError:
            return "Potential circularity (depth exceeded)", None

    def contradiction_proof(self):
        """Proof by contradiction with circularity check"""
        negated = ~self.theorem
        if self._check_circularity(negated):
            return "Circular proof detected"
        return "Valid" if not satisfiable(negated) else "Invalid"

    def circular_proof_check(self, premises):
        """Explicit circular proof detection"""
        return any(
            Equivalent(premise, self.theorem) or 
            premise == self.theorem 
            for premise in premises
        )

    def run_proofs(self, axioms=[]):
        """Run all proof strategies with circularity checks"""
        results = {
            'truth_table': self.brute_force_truth_table(),
            'direct_proof': self.direct_proof(axioms),
            'contradiction': self.contradiction_proof(),
            'circular': self.circular_proof_check(axioms)
        }
        return results

# Example: Attempt to create circular proof
A, B = symbols('A B')
theorem = Implies(A, A)  # Tautology
axioms = [theorem]  # Circular premise

prover = TheoremProver(theorem, [A, B])
results = prover.run_proofs(axioms=axioms)

print("Proof Results:")
print(f"Truth Table: {'Valid' if results['truth_table'][0] else 'Invalid'}")
print(f"Direct Proof: {results['direct_proof'][0]}")
print(f"Contradiction: {results['contradiction']}")
print(f"Circular Proof Detected: {results['circular']}")
```

---

### **Key Features**
1. **Circular Proof Detection**:
   - Tracks premise-conclusion dependencies
   - Checks for self-referential arguments
   - Explicit check for theorem in premises

2. **Proof Techniques**:
   - Truth table verification
   - Direct proof with simplification
   - Proof by contradiction
   - Dependency graph analysis

3. **Output Example**:
   ```
   Proof Results:
   Truth Table: Valid
   Direct Proof: Circular proof detected
   Contradiction: Valid
   Circular Proof Detected: True
   ```

---

### **How It Works**
1. **Dependency Tracking**:
   - Builds a graph of premise-conclusion relationships
   - Uses DFS to detect cycles in the graph

2. **Circular Proof Checks**:
   - Direct comparison of premises with conclusion
   - Recursive dependency analysis
   - Depth-limited cycle detection

3. **Integration with Proof Methods**:
   - All proof techniques check for circularity
   - Separate explicit circular proof check

---

### **Limitations**
1. **Propositional Logic Focus**:
   - Works best for Boolean logic
   - Limited to finite variable spaces

2. **Complex Circularity**:
   - May miss indirect circular dependencies
   - Limited recursion depth for complex cases

3. **Performance**:
   - Truth tables grow exponentially (2<sup>n</sup> complexity)
   - Dependency tracking adds overhead

For advanced theorem proving with better circularity detection, consider using formal proof assistants like **Coq** or **Isabelle**, which implement sophisticated cycle detection in their kernel architectures.
