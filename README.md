# 🧠 SAT Solver: Resolution vs. DPLL

This repository contains a Python-based SAT solver that supports both the **Resolution method** and the **DPLL algorithm**. It was developed for academic purposes to demonstrate and compare classical methods for solving Boolean Satisfiability (SAT) problems.

## ▶️ How to Run

Make sure you have Python 3.10+ installed.

Clone this repository and run:

```bash
python main.py

## 🧪 How to Run the Experiments

For each test case:

1. Select option `1` and enter a CNF formula.
2. Choose option `2` to check if the formula is well-formed.
3. Run the Resolution solver with option `12`.
4. Run the DPLL solver with option `13`.

Both solvers will display:

- Whether the formula is SAT or UNSAT
- Intermediate steps and derivations
- Runtime (in milliseconds)
- Number of steps or recursive calls

---

## 🧾 Test Formulas Used

The following CNF formulas were used in the experiment:

- `((P|Q)&(-P)&(-Q))`
- `((A|B)&(-A)&((-A)|C)&(-C)&((-C)|B))`
- `((X|Y)&(-X)&((-X)|Z)&(-Y)&(-Z)&((-Y)|(-Z)))`
- `((P|Q)&(-Q)&((-Q)|R)&(-P)&(-R)&((-P)|(-R)))`
- `((A|B|C)&((-A)|D)&((-B)|E)&(-D)&(-E)&(-C))`
- `((M|N)&(-M)&(-N)&((-M)|(-N))&((-M)|N))`
- `((A|B)&(-A)&(B))`
- `((A|B)&((-A)|C)&(C|B))`
