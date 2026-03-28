# FormalButterfly

A Lean 4 formalization of theorems on **collinearity** and **cocircularity** (concyclic points) in Euclidean geometry.

## Overview

This project formalizes basic geometric theorems about point configurations in the Euclidean plane (ℝ²). The project demonstrates how to use determinants to determine if a set of points is collinear or concyclic.

### Key Results

- **Collinearity Test**: Three points p, q, r are collinear if and only if the determinant of their augmented matrix equals zero
  ```lean
  lemma collinear_iff_det_zero (p q r : Point) :
    Collinear ℝ ({p, q, r} : Set Point) ↔ collinearDet p q r = 0
