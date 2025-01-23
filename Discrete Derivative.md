# Discrete derivatives

Ah, **discrete derivatives** (also called finite differences) are a powerful tool for analyzing sequences or discrete functions, which is exactly what algorithm runtimes are! Let’s reframe your question:

**Goal**: Calculate the growth rate (time complexity) of a famous algorithm using **discrete derivatives** (differences between consecutive terms of the runtime function \( T(n) \)).

---

### What is a Discrete Derivative?
For a function \( T(n) \) (e.g., runtime of an algorithm for input size \( n \)), the **discrete derivative** is:
\[
\Delta T(n) = T(n+1) - T(n).
\]
This measures how much \( T(n) \) increases as \( n \) grows by 1. The pattern of \( \Delta T(n) \) reveals the asymptotic growth rate (e.g., \( O(1) \), \( O(n) \), \( O(n^2) \), etc.).

---

### Step-by-Step Analysis with Examples

#### **1. Constant Time: \( O(1) \)**
- **Algorithm**: Accessing an array element (e.g., `arr[i]`).
- **Runtime**: \( T(n) = 1 \) (independent of \( n \)).
- **Discrete Derivative**:
  \[
  \Delta T(n) = T(n+1) - T(n) = 1 - 1 = 0.
  \]
- **Interpretation**: \( \Delta T(n) = 0 \) implies **no growth** → \( O(1) \).

---

#### **2. Linear Time: \( O(n) \)**
- **Algorithm**: Linear search (iterating through a list).
- **Runtime**: \( T(n) = n \).
- **Discrete Derivative**:
  \[
  \Delta T(n) = (n+1) - n = 1.
  \]
- **Interpretation**: \( \Delta T(n) = 1 \) (**constant growth**) → \( O(n) \).

---

#### **3. Quadratic Time: \( O(n^2) \)**
- **Algorithm**: Bubble sort (nested loops).
- **Runtime**: \( T(n) = n^2 \).
- **Discrete Derivative**:
  \[
  \Delta T(n) = (n+1)^2 - n^2 = 2n + 1.
  \]
- **Interpretation**: \( \Delta T(n) = 2n + 1 \) (**linear growth**) → Original \( T(n) \) is \( O(n^2) \).

---

#### **4. Logarithmic Time: \( O(\log n) \)**
- **Algorithm**: Binary search.
- **Runtime**: \( T(n) = \log_2 n \) (approximate steps).
- **Discrete Derivative**:
  \[
  \Delta T(n) = \log_2(n+1) - \log_2 n = \log_2\left(1 + \frac{1}{n}\right) \approx \frac{1}{n \ln 2} \text{ (for large \( n \))}.
  \]
- **Interpretation**: \( \Delta T(n) \to 0 \) as \( n \to \infty \) (**decaying growth**) → \( O(\log n) \).

---

#### **5. Linearithmic Time: \( O(n \log n) \)**
- **Algorithm**: Merge sort.
- **Runtime**: \( T(n) = n \log_2 n \).
- **Discrete Derivative**:
  \[
  \Delta T(n) = (n+1)\log_2(n+1) - n \log_2 n.
  \]
  Simplify using \( \log_2(n+1) \approx \log_2 n + \frac{1}{n \ln 2} \):
  \[
  \Delta T(n) \approx \log_2 n + \frac{1}{\ln 2}.
  \]
- **Interpretation**: \( \Delta T(n) \approx \log n \) (**logarithmic growth**) → Original \( T(n) \) is \( O(n \log n) \).

---

#### **6. Exponential Time: \( O(2^n) \)**
- **Algorithm**: Naive recursive Fibonacci.
- **Runtime**: \( T(n) = 2^n \).
- **Discrete Derivative**:
  \[
  \Delta T(n) = 2^{n+1} - 2^n = 2^n.
  \]
- **Interpretation**: \( \Delta T(n) = 2^n \) (**exponential growth**) → \( O(2^n) \).

---

### General Rule of Thumb
The growth rate of \( \Delta T(n) \) determines the asymptotic class of \( T(n) \):
- \( \Delta T(n) = O(1) \) → \( T(n) = O(n) \).
- \( \Delta T(n) = O(n) \) → \( T(n) = O(n^2) \).
- \( \Delta T(n) = O(\log n) \) → \( T(n) = O(n \log n) \).
- \( \Delta T(n) = O(2^n) \) → \( T(n) = O(2^n) \).

---

### Why This Works
- **Discrete derivatives** act like "slopes" for discrete functions. The pattern of these slopes directly maps to the asymptotic behavior of \( T(n) \).
- This mirrors how continuous derivatives classify growth rates in calculus (e.g., \( f'(x) = \text{constant} \implies f(x) \) is linear).

---

### Final Answer
By calculating the discrete derivative \( \Delta T(n) = T(n+1) - T(n) \), you can classify the growth rate of an algorithm:
- **Example**: If \( \Delta T(n) = 3n + 2 \), then \( T(n) = O(n^2) \).
- **Practice**: Try this for quicksort (\( O(n \log n) \)) or matrix multiplication (\( O(n^3) \))!
