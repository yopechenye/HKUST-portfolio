# Formal Verification of Pell Equations in Lean 4

**A computer-verified proof of the infinitude of integer solutions to Pell's equation**

## 1. Project Overview

This project investigates the classical Pell equation:

**x² − dy² = 1**

where x and y are integers and d is an integer parameter.

Using **Lean 4** and **Mathlib**, I formalized algebraic properties of Pell equation solutions and implemented a recursive algorithm for generating new solutions from a known one.

The main objective was to formally verify the correctness of this algorithm and prove that the equation

**x² − 2y² = 1**

has infinitely many integer solutions.

## 2. Mathematical Foundations

### Multiplication of Solutions

Given two solutions (x₁, y₁) and (x₂, y₂), define their product as:

**(x₁, y₁) ⋆ (x₂, y₂) = (x₁x₂ + dy₁y₂, x₁y₂ + x₂y₁)**

The key algebraic identity is:

**(x₁x₂ + dy₁y₂)² − d(x₁y₂ + x₂y₁)² = (x₁² − dy₁²)(x₂² − dy₂²)**

Therefore, multiplying two Pell equation solutions produces another valid solution.

### Recursive Solution Generator

Starting from the neutral solution:

**S₀ = (1, 0)**

we define:

**Sₙ₊₁ = Sₙ ⋆ (a, b)**

where (a, b) is a known solution.

For d = 2 and (a, b) = (3, 2), the algorithm generates:

| n |  x |  y |

| 0 |  1 |  0 |
| 1 |  3 |  2 |
| 2 |  17|  12|
| 3 |  99|  70|
| 4 | 577| 408|

Every generated pair satisfies x² − 2y² = 1.

## 3. Formally Verified Results

The following theorems are implemented and verified in Lean 4:


pell_2_example  Verifies that (3, 2) solves the equation for d = 2 

pell_one_zero  Proves that (1, 0) is a solution for every integer d 

pellMul_correct  Proves closure under multiplication 

pellSeq_correct  Verifies that the recursive generator always produces valid solutions 

pellSeq_positive  Proves bounds on generated coordinates under positivity assumptions 

pellSeq_strictIncrease  Proves strict growth of the first coordinate 

pellSeq_injective  Proves that different indices give different first coordinates 

pell_infinite  Proves the infinitude of integer solutions for d = 2 

### Main Theorem

**The equation x² − 2y² = 1 has infinitely many integer solutions.**

The proof consists of four principal steps:

1. Establish that the multiplication operation preserves valid solutions.
2. Prove the correctness of the recursive generator by induction.
3. Establish strict growth and injectivity of the resulting sequence.
4. Use injectivity to prove that the set of generated solutions, and therefore the set of all solutions, is infinite.

The final statement is formally verified by Lean.

## 4. Implementation

**Programming language:** Lean 4

**Mathematical library:** Mathlib

**Research areas:** Number Theory, Formal Verification, Recursive Algorithms

The implementation includes three main definitions:

- `Pell_sol` — defines the mathematical condition for a valid Pell solution.
- `pellMul` — implements the multiplication operation.
- `pellSeq` — recursively generates solution pairs.

The proofs use mathematical induction, algebraic transformations, rewriting, inequalities, and established theorems from Mathlib.

### Source Code

The main implementation is located at:

`HKUST portfolio/Pell.lean`

## 5. How to Run the Project

1. Install Lean 4 using the [elan version manager](https://github.com/leanprover/elan).
2. Clone or download this GitHub repository.
3. Open the project folder in Visual Studio Code with the Lean 4 extension installed.
4. Open a terminal in the root directory of the project.
5. Run the following commands to download dependencies and verify the proofs:

```bash
lake exe cache get
lake env lean "HKUST portfolio/Pell.lean"
```

The first command retrieves precompiled Mathlib dependencies when available.

The second checks the Lean source file.

Successful verification means Lean accepts the definitions and proofs without errors.

## 6. Scope and Future Work

The current project formally proves that the equation **x² − 2y² = 1** has infinitely many integer solutions.

It also establishes general properties of solution multiplication and recursive generation.

Possible future extensions include:

- Finding fundamental solutions of Pell equations.
- Developing continued-fraction algorithms.
- Formally proving the completeness of solution-generation methods.
- Comparing the computational efficiency of different algorithms.

These are proposed directions for further research and are not claimed as completed results.

## 7. Motivation

I began studying Lean 4 independently through the Natural Number Game.

After learning fundamental proof techniques, I wanted to apply them to a more substantial mathematical problem rather than isolated exercises.

Pell equations attracted my interest because a relatively simple equation leads to rich algebraic structures, recursive sequences, and questions about infinitely many integer solutions.

Through this project, I explored how mathematical arguments can be translated into computer-verifiable proofs and how complex results can be constructed from a sequence of smaller, rigorously verified lemmas.

This experience strengthened my interest in mathematics, theoretical computer science, and formal verification.
