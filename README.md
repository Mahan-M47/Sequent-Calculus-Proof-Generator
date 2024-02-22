# Sequent-Calculus-Proof-Generator

This Python program generates proofs in sequent calculus for given logical formulas. Sequent Calculus is a style of formal logical argumentation with one logical axiom and several logical rules.

Utilizing RegEx and recursive functions. this program generates a step-by-step proof for logical expression written in a standard format.

You can try the following examples as input:
```
  =>(∃x(A->B))->((∀xA)->B)

  =>((∃xA)->B)->(∀x(A->B))

  =>(~(∀xA))->(∃x~A)
```
