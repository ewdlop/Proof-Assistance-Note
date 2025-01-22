# README

## Welcome to the jsCoq Interactive Online System!

[https://vercel.com/](https://coq.vercel.app/)

## Do I run the coq in a different program?

Yes, Coq requires its own dedicated environment to run and interact with proofs and definitions. Here are the main ways you can work with Coq:

### 1. **CoqIDE (Coq Integrated Development Environment)**  
   - CoqIDE is the official IDE for Coq.  
   - It provides an environment where you can write and execute Coq proofs interactively.
   - **Steps to Install and Use**:
     1. Install Coq and CoqIDE from the [official Coq website](https://coq.inria.fr/).
     2. Open CoqIDE and write your `.v` Coq scripts.
     3. Use the provided interface to step through proofs or execute commands.

---

### 2. **Proof General + Emacs**  
   - **Proof General** is a popular extension for Emacs, designed for proof assistants like Coq.
   - **Steps to Install and Use**:
     1. Install Emacs and Proof General. Instructions are available [here](https://proofgeneral.github.io/).
     2. Open `.v` files in Emacs, and interactively run Coq proofs with commands.

---

### 3. **VS Code with Coq Extension**  
   - Visual Studio Code offers a more modern interface with the [Coq Extension](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq).
   - **Steps to Install and Use**:
     1. Install Visual Studio Code.
     2. Install the "Coq" extension from the Extensions Marketplace.
     3. Write `.v` files and execute Coq commands within VS Code.

---

### 4. **Coq Command-Line Tool**  
   - If you prefer running Coq in a terminal, you can use the `coqc` command.
   - **Steps to Use**:
     1. Write your code in a file, e.g., `file.v`.
     2. Run `coqc file.v` in your terminal to compile and check the file.

---

### 5. **Online Platforms**  
   - Use online tools to experiment with Coq without installing anything:
     - **[CoqIDE Online](https://coq.vercel.app/)** or **[CoqLive](https://x80.org/collacoq/)**.
     - Write and test Coq scripts directly in your browser.

---

### Recommended Setup  
If you're new to Coq, starting with **CoqIDE** or the **VS Code extension** is the easiest way to get familiar with the environment. Over time, you can experiment with other options as you develop your expertise. Let me know if you'd like guidance on setting up any of these environments!
