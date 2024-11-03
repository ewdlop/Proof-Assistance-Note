# Proof-Assistance-Note


https://ncatlab.org/nlab/show/type%2Btheory#:~:text=Type%20theory%20is%20a%20branch%20of%20mathematical%20symbolic,the%20type%20of%20a%20function%20between%20natural%20numbers.

https://zh.wikipedia.org/wiki/%E4%BE%9D%E8%B5%96%E7%B1%BB%E5%9E%8B

https://fstar-lang.org/

https://lean-lang.org/documentation/


# Gödel's Theorem to Gödel AI: The Blueprint for Self-Learning Machines

Who knows and who c who caresareeessss

https://www.youtube.com/watch?v=gIJXcGQrpoM&t=1450s



# Class hierarchies 

Class hierarchies in computational complexity and logic theory are frameworks for categorizing problems, functions, or sets according to their complexity or structural properties. Each hierarchy you've listed—**Polynomial Hierarchy**, **Exponential Hierarchy**, **Grzegorczyk Hierarchy**, **Arithmetical Hierarchy**, and **Boolean Hierarchy**—has a distinct purpose and applies different criteria to organize classes within the hierarchy. Here’s an overview of each:

---

### 1. **Polynomial Hierarchy (PH)**

The **Polynomial Hierarchy** is a hierarchy of complexity classes that generalizes **P** (problems solvable in polynomial time) and **NP** (nondeterministic polynomial time) by introducing alternating quantifiers.

- **Levels of the Polynomial Hierarchy**: The polynomial hierarchy is structured in levels (often denoted by \(\Sigma_k^P\) and \(\Pi_k^P\)), where each level represents a class of problems that can be solved by alternating sequences of **existential** and **universal quantifiers** over polynomial-time computations.
    - **\(\Sigma_1^P\) = NP**: Problems that can be solved in nondeterministic polynomial time.
    - **\(\Pi_1^P\) = co-NP**: Problems whose complements are in NP.
    - **\(\Sigma_2^P\)**: Exists-Forall problems, solvable by a nondeterministic polynomial algorithm with an existential quantifier followed by a universal quantifier.
    - Higher levels (\(\Sigma_k^P\) and \(\Pi_k^P\)) continue by alternating quantifiers.

- **Relationship with Complexity Classes**: If the Polynomial Hierarchy collapses to some level \(k\), it means that all levels above \(k\) are equivalent, which would imply significant simplifications in complexity theory.

- **Importance**: The Polynomial Hierarchy captures a wide range of natural computational problems and is essential in understanding the structure of NP and co-NP and the implications for related classes.

---

### 2. **Exponential Hierarchy (EH)**

The **Exponential Hierarchy** is a hierarchy of complexity classes similar to the Polynomial Hierarchy but based on **exponential time bounds**.

- **Definition**: Each level in the Exponential Hierarchy corresponds to the classes \(\Sigma_k^{\text{EXP}}\) and \(\Pi_k^{\text{EXP}}\), where:
    - \(\Sigma_1^{\text{EXP}} = \text{NEXP}\): Nondeterministic exponential time.
    - \(\Pi_1^{\text{EXP}} = \text{co-NEXP}\): Complement of NEXP problems.
    - \(\Sigma_2^{\text{EXP}}\): Exists-Forall problems solvable in exponential time.
  
- **Hierarchy Structure**: The hierarchy allows alternating quantifiers, with each level increasing the bounds of computation resources exponentially rather than polynomially.

- **Importance**: The Exponential Hierarchy is crucial for understanding problems that require exponentially more resources than those in the Polynomial Hierarchy. It’s particularly relevant in areas where problems grow exponentially with input size, like certain types of logical reasoning or combinatorial problems.

---

### 3. **Grzegorczyk Hierarchy**

The **Grzegorczyk Hierarchy** is a classification of functions based on **computational complexity** with respect to **primitive recursion** and **growth rate**.

- **Levels of the Grzegorczyk Hierarchy**: The hierarchy has levels \(E_n\), where:
    - \(E_0\) is the class of **constant functions**.
    - \(E_1\) contains **addition** functions.
    - \(E_2\) includes **multiplication** and functions with polynomial growth.
    - Higher levels \(E_n\) contain functions that grow at increasingly faster rates.
  
- **Relation to Computability**: Each level of the Grzegorczyk Hierarchy corresponds to a class of computable functions with restricted growth rates, and \(E_3\) includes all **primitive recursive functions**. Beyond a certain level, the hierarchy includes functions that are not primitive recursive but still computable.

- **Importance**: This hierarchy is fundamental in **computability theory** and **recursion theory**. It provides insights into the growth rates of functions that are still computable and highlights the boundaries between primitive recursive functions and more complex forms of computation.

---

### 4. **Arithmetical Hierarchy**

The **Arithmetical Hierarchy** is used in **mathematical logic** and **recursion theory** to classify **sets of natural numbers** (or statements) based on the **quantifier complexity** of their logical definitions.

- **Levels of the Arithmetical Hierarchy**: Levels are defined using \(\Sigma_n\) and \(\Pi_n\) notation, where:
    - \(\Sigma_0 = \Pi_0 = \Delta_0\): Decidable (computable) sets.
    - \(\Sigma_1\): Sets definable with an **existential quantifier** followed by a computable predicate.
    - \(\Pi_1\): Sets definable with a **universal quantifier** followed by a computable predicate.
    - Higher levels alternate quantifiers.
  
- **Applications**: The hierarchy classifies logical statements based on their complexity, which is useful for understanding **provability** and **decidability** in formal systems. For example, \(\Sigma_1\)-statements include existential questions about natural numbers, while \(\Pi_1\)-statements include universal questions.

- **Importance**: The Arithmetical Hierarchy provides a framework for analyzing the **complexity of mathematical statements**, particularly in fields like **model theory** and **proof theory**.

---

### 5. **Boolean Hierarchy**

The **Boolean Hierarchy** builds on **NP** and is a hierarchy of complexity classes created by **combining NP sets with Boolean operations** like union, intersection, and complementation.

- **Levels in the Boolean Hierarchy**:
    - The hierarchy begins with **NP** (problems solvable by nondeterministic polynomial-time algorithms).
    - The next levels are formed by taking **Boolean combinations** of NP sets, such as:
        - **NP ∩ co-NP**: Problems that belong to both NP and co-NP.
        - **(NP ∩ co-NP) ∪ NP**: The union of NP and problems in both NP and co-NP.
        - Higher levels involve increasingly complex combinations.
  
- **Importance**: The Boolean Hierarchy is critical in understanding how NP problems interact with co-NP problems and provides insights into the complexity of **Boolean operations** on NP problems. It helps clarify relationships between different classes within NP and their interactions with co-NP.

---

### Summary Table

| Hierarchy              | Focus Area             | Key Features                                                                                  |
|------------------------|------------------------|-----------------------------------------------------------------------------------------------|
| **Polynomial Hierarchy (PH)** | Complexity Theory     | Alternating quantifiers over polynomial time; generalizes NP and co-NP.                         |
| **Exponential Hierarchy (EH)** | Complexity Theory     | Alternating quantifiers over exponential time; captures higher complexity problems.             |
| **Grzegorczyk Hierarchy**     | Computability Theory  | Classifies functions by growth rate; includes primitive recursive and hyper-primitive classes. |
| **Arithmetical Hierarchy**    | Mathematical Logic    | Categorizes sets/statements by quantifier complexity; used in recursion and proof theory.      |
| **Boolean Hierarchy**         | Complexity Theory     | Layers Boolean combinations of NP problems; studies interactions between NP and co-NP.         |

---

These hierarchies provide **structured ways to analyze complexity** and **logical properties** across different domains of theoretical computer science and mathematical logic. Each hierarchy serves a distinct purpose, from understanding polynomial-time computations to exploring logical quantifier depth, making them fundamental tools for formalizing and studying computational and logical problems.
