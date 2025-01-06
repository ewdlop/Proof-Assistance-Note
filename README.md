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

- **Levels of the Polynomial Hierarchy**: The polynomial hierarchy is structured in levels (often denoted by \$\Sigma_k^P\$ and \$\Pi_k^P\$), where each level represents a class of problems that can be solved by alternating sequences of **existential** and **universal quantifiers** over polynomial-time computations.
    - **\$\Sigma_1^P\$ = NP**: Problems that can be solved in nondeterministic polynomial time.
    - **\$\Pi_1^P\$ = co-NP**: Problems whose complements are in NP.
    - **\$\Sigma_2^P\$**: Exists-Forall problems, solvable by a nondeterministic polynomial algorithm with an existential quantifier followed by a universal quantifier.
    - Higher levels (\$\Sigma_k^P\$ and \$\Pi_k^P\$) continue by alternating quantifiers.

- **Relationship with Complexity Classes**: If the Polynomial Hierarchy collapses to some level \$k\$, it means that all levels above \$k\$ are equivalent, which would imply significant simplifications in complexity theory.

- **Importance**: The Polynomial Hierarchy captures a wide range of natural computational problems and is essential in understanding the structure of NP and co-NP and the implications for related classes.

---

### 2. **Exponential Hierarchy (EH)**

The **Exponential Hierarchy** is a hierarchy of complexity classes similar to the Polynomial Hierarchy but based on **exponential time bounds**.

- **Definition**: Each level in the Exponential Hierarchy corresponds to the classes \$\Sigma_k^{\text{EXP}}\$ and \$\Pi_k^{\text{EXP}}\$, where:
    - \$\Sigma_1^{\text{EXP}} = \text{NEXP}\$: Nondeterministic exponential time.
    - \$\Pi_1^{\text{EXP}} = \text{co-NEXP}\$: Complement of NEXP problems.
    - \$\Sigma_2^{\text{EXP}}\$: Exists-Forall problems solvable in exponential time.
  
- **Hierarchy Structure**: The hierarchy allows alternating quantifiers, with each level increasing the bounds of computation resources exponentially rather than polynomially.

- **Importance**: The Exponential Hierarchy is crucial for understanding problems that require exponentially more resources than those in the Polynomial Hierarchy. It’s particularly relevant in areas where problems grow exponentially with input size, like certain types of logical reasoning or combinatorial problems.

---

### 3. **Grzegorczyk Hierarchy**

The **Grzegorczyk Hierarchy** is a classification of functions based on **computational complexity** with respect to **primitive recursion** and **growth rate**.

- **Levels of the Grzegorczyk Hierarchy**: The hierarchy has levels \$E_n\$, where:
    - \$E_0\$ is the class of **constant functions**.
    - \$E_1\$ contains **addition** functions.
    - \$E_2\$ includes **multiplication** and functions with polynomial growth.
    - Higher levels \$E_n\$ contain functions that grow at increasingly faster rates.
  
- **Relation to Computability**: Each level of the Grzegorczyk Hierarchy corresponds to a class of computable functions with restricted growth rates, and \$E_3\$ includes all **primitive recursive functions**. Beyond a certain level, the hierarchy includes functions that are not primitive recursive but still computable.

- **Importance**: This hierarchy is fundamental in **computability theory** and **recursion theory**. It provides insights into the growth rates of functions that are still computable and highlights the boundaries between primitive recursive functions and more complex forms of computation.

---

### 4. **Arithmetical Hierarchy**

The **Arithmetical Hierarchy** is used in **mathematical logic** and **recursion theory** to classify **sets of natural numbers** (or statements) based on the **quantifier complexity** of their logical definitions.

- **Levels of the Arithmetical Hierarchy**: Levels are defined using \$\Sigma_n\$ and \$\Pi_n\$ notation, where:
    - \$\Sigma_0 = \Pi_0 = \Delta_0\$: Decidable (computable) sets.
    - \$\Sigma_1\$: Sets definable with an **existential quantifier** followed by a computable predicate.
    - \$\Pi_1\$: Sets definable with a **universal quantifier** followed by a computable predicate.
    - Higher levels alternate quantifiers.
  
- **Applications**: The hierarchy classifies logical statements based on their complexity, which is useful for understanding **provability** and **decidability** in formal systems. For example, \$\Sigma_1\$-statements include existential questions about natural numbers, while \$\Pi_1\$-statements include universal questions.

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

# Dependent Type?

https://en.wikipedia.org/wiki/Dependent_type

https://web.archive.org/web/20201109032232/http://sage.soe.ucsc.edu/

# 推理規則

### 修正後的用文的句子
在基於推理規則的證明中，常用的寫法包括以下幾種：

1. **直接推理**：
   - 前提：\( A \rightarrow B \)
   - 前提：\( B \rightarrow C \)
   - 結論：\( A \rightarrow C \) （通過 **連鎖律** (Hypothetical Syllogism)）

2. **反證法**：
   - 前提：假設 \( \neg P \) 為真
   - 推導出矛盾：\( Q \land \neg Q \)
   - 結論：\( P \) 必為真 （通過 **歸謬法** (Reductio ad Absurdum)）

3. **反證法（Contrapositive）**：
   - 前提：\( A \rightarrow B \)
   - 反證：\( \neg B \rightarrow \neg A \) （通過 **對換律** (Contraposition)）
   - 結論：若反證為真，則原命題 \( A \rightarrow B \) 為真。

4. **歸謬法**：
   - 假設：\( P \)
   - 得出矛盾：\( \neg Q \)
   - 結論：\( \neg P \) 必為真（通過 **矛盾律** (Contradiction)）

5. **循環證明**：
   - 前提：\( A_1 \rightarrow A_2 \)
   - 前提：\( A_2 \rightarrow A_3 \)
   - ⋮
   - 前提：\( A_{n-1} \rightarrow A_n \)
   - 前提：\( A_n \rightarrow A_1 \)
   - 結論：所有命題 \( A_1, A_2, \dots, A_n \) 均為真 （通過 **循環推理** (Cyclic Reasoning)）

6. **數學歸納法**：
   - 基礎步驟：證明 \( P(1) \) 為真
   - 歸納步驟：假設 \( P(k) \) 為真，證明 \( P(k+1) \) 為真 （通過 **數學歸納法** (Mathematical Induction)）
   - 結論：\( P(n) \) 對所有自然數 \( n \) 為真

### 中文
在基於推理規則的證明中，常用的寫法包括以下幾種：

1. **直接推理**：
   - 前提：\( A \rightarrow B \)
   - 前提：\( B \rightarrow C \)
   - 結論：\( A \rightarrow C \) （通過 **連鎖律** (Hypothetical Syllogism)）

2. **反證法**：
   - 前提：假設 \( \neg P \) 為真
   - 推導出矛盾：\( Q \land \neg Q \)
   - 結論：\( P \) 必為真 （通過 **歸謬法** (Reductio ad Absurdum)）

3. **反證法（Contrapositive）**：
   - 前提：\( A \rightarrow B \)
   - 反證：\( \neg B \rightarrow \neg A \) （通過 **對換律** (Contraposition)）
   - 結論：若反證為真，則原命題 \( A \rightarrow B \) 為真。

4. **歸謬法**：
   - 假設：\( P \)
   - 得出矛盾：\( \neg Q \)
   - 結論：\( \neg P \) 必為真（通過 **矛盾律** (Contradiction)）

5. **循環證明**：
   - 前提：\( A_1 \rightarrow A_2 \)
   - 前提：\( A_2 \rightarrow A_3 \)
   - ⋮
   - 前提：\( A_{n-1} \rightarrow A_n \)
   - 前提：\( A_n \rightarrow A_1 \)
   - 結論：所有命題 \( A_1, A_2, \dots, A_n \) 均為真 （通過 **循環推理** (Cyclic Reasoning)）

6. **數學歸納法**：
   - 基礎步驟：證明 \( P(1) \) 為真
   - 歸納步驟：假設 \( P(k) \) 為真，證明 \( P(k+1) \) 為真 （通過 **數學歸納法** (Mathematical Induction)）
   - 結論：\( P(n) \) 對所有自然數 \( n \) 為真

### 正式英文
In proofs based on rules of inference, the typical formats include:

1. **Direct Reasoning**:
   - Premise: \( A \rightarrow B \)
   - Premise: \( B \rightarrow C \)
   - Conclusion: \( A \rightarrow C \) (using **Hypothetical Syllogism**)

2. **Proof by Contradiction**:
   - Premise: Assume \( \neg P \)
   - Derive a contradiction: \( Q \land \neg Q \)
   - Conclusion: \( P \) must be true (using **Reductio ad Absurdum**)

3. **Proof by Contrapositive**:
   - Premise: \( A \rightarrow B \)
   - Contrapositive: \( \neg B \rightarrow \neg A \) (using **Contraposition**)
   - Conclusion: If the contrapositive is true, then the original proposition \( A \rightarrow B \) is true.

4. **Proof by Contradiction**:
   - Assume: \( P \)
   - Derive a contradiction: \( \neg Q \)
   - Conclusion: \( \neg P \) must be true (using **Contradiction**)

5. **Cyclic Proof**:
   - Premise: \( A_1 \rightarrow A_2 \)
   - Premise: \( A_2 \rightarrow A_3 \)
   - ⋮
   - Premise: \( A_{n-1} \rightarrow A_n \)
   - Premise: \( A_n \rightarrow A_1 \)
   - Conclusion: All propositions \( A_1, A_2, \dots, A_n \) are true (using **Cyclic Reasoning**)

6. **Mathematical Induction**:
   - Base case: Prove \( P(1) \) is true
   - Inductive step: Assume \( P(k) \) is true, prove \( P(k+1) \) is true (using **Mathematical Induction**)
   - Conclusion: \( P(n) \) is true for all natural numbers \( n \)

### 西班牙文
En las pruebas basadas en reglas de inferencia, los formatos típicos incluyen:

1. **Razonamiento Directo**:
   - Premisa: \( A \rightarrow B \)
   - Premisa: \( B \rightarrow C \)
   - Conclusión: \( A \rightarrow C \) (usando **Silogismo Hipotético**)

2. **Prueba por Contradicción**:
   - Premisa: Supongamos \( \neg P \)
   - Derivamos una contradicción: \( Q \land \neg Q \)
   - Conclusión: \( P \) debe ser verdadero (usando **Reducción al Absurdo**)

3. **Prueba por Contraposición**:
   - Premisa: \( A \rightarrow B \)
   - Contraposición: \( \neg B \rightarrow \neg A \) (usando **Contraposición**)
   - Conclusión: Si la contraposición es verdadera, entonces la proposición original \( A \rightarrow B \) es verdadera.

4. **Prueba por Contradicción**:
   - Supuesto: \( P \)
   - Derivamos una contradicción: \( \neg Q \)
   - Conclusión: \( \neg P \) debe ser verdadero (usando **Contradicción**)

5. **Prueba Cíclica**:
   - Premisa: \( A_1 \rightarrow A_2 \)
   - Premisa: \( A_2 \rightarrow A_3 \)
   - ⋮
   - Premisa: \( A_{n-1} \rightarrow A_n \)
   - Premisa: \( A_n \rightarrow A_1 \)
   - Conclusión: Todas las proposiciones \( A_1, A_2, \dots, A_n \) son verdaderas (usando **Razonamiento Cíclico**)

6. **Inducción Matemática**:
   - Caso base: Probar que \( P(1) \) es verdadero
   - Paso inductivo: Suponer que \( P(k) \) es verdadero, probar que \( P(k+1) \) es verdadero (usando **Inducción Matemática**)
   - Conclusión: \( P(n) \
  
## Physics Fact Derivation Matter(S) ? :

Matters or not. Does it matters?  It is a mater? Are they matters? Do they matter? English majors. English majores in majors. English majores.

None of it matters because nobody cares.

## p => ~p (Circular Reasoning)

## p & ~p (logical contradiction)

## The logical statement \( p \Rightarrow q \) ("if \( p \), then \( q \)") is **logically equivalent to** the following:

---

### **1. Contrapositive**
\[
\neg q \Rightarrow \neg p
\]
- Meaning: "If \( q \) is false, then \( p \) is false."
- This equivalence holds because \( p \Rightarrow q \) is true in all cases where \( q \) is true or \( p \) is false.

---

### **2. Disjunction Form**
\[
\neg p \lor q
\]
- Meaning: "Either \( p \) is false, or \( q \) is true."
- This is derived from the truth table for \( p \Rightarrow q \), which is true except when \( p \) is true and \( q \) is false.

---

### **3. Negation Form**
\[
\neg (p \land \neg q)
\]
- Meaning: "It is not the case that \( p \) is true and \( q \) is false."
- This highlights that the only condition where \( p \Rightarrow q \) is false is when \( p \) is true and \( q \) is false.

---

### **4. Using De Morgan's Laws**
Breaking it down further, \( p \Rightarrow q \) can also be expressed as:
\[
\neg p \lor q \equiv \neg (p \land \neg q)
\]
This demonstrates the equivalence between the disjunction and negation forms.

---

### **Truth Table Validation**

| \( p \) | \( q \) | \( p \Rightarrow q \) | \( \neg p \lor q \) | \( \neg (p \land \neg q) \) | \( \neg q \Rightarrow \neg p \) |
|--------|--------|-----------------------|--------------------|---------------------------|-----------------------------|
| T      | T      | T                     | T                  | T                         | T                           |
| T      | F      | F                     | F                  | F                         | F                           |
| F      | T      | T                     | T                  | T                         | T                           |
| F      | F      | T                     | T                  | T                         | T                           |

All these forms are equivalent.

---

Would you like a deeper dive into any specific representation or proof?
