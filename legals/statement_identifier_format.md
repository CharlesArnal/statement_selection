# Statement Identifier Format

## Context

We are building a benchmark of mathematical statements for autoformalization (translating informal mathematics into the Lean 4 proof assistant). Each statement in the benchmark may be associated with metadata that records where it comes from and how to locate it in the source material.

This document describes the identifier format and provides two examples for review.

## Identifier Schema

Each statement is identified by five fields:

| Field | Description |
|-------|-------------|
| `source` | Title of the book or course the statement is taken from |
| `url` | URL where the source material can be downloaded or accessed |
| `statement_type` | Theorem, Lemma, Proposition, Corollary, or Claim |
| `statement_number` | Numbering from the source (e.g., 1.4.2) |
| `statement_name` | Common name, if applicable (e.g., Kővári–Sós–Turán theorem); omitted when none exists |

## Example 1: Book

**Source**: *Graph Theory and Additive Combinatorics* (Yufei Zhao, Cambridge University Press, 2023)

| Field | Value |
|-------|-------|
| `source` | Graph Theory and Additive Combinatorics |
| `url` | https://yufeizhao.com/gtac/gtac.pdf |
| `statement_type` | Theorem |
| `statement_number` | 1.4.2 |
| `statement_name` | Kővári–Sós–Turán theorem |

## Example 2: Online Course

**Source**: MIT OCW 18.S997 *High-Dimensional Statistics* (Philippe Rigollet, Spring 2015)

| Field | Value |
|-------|-------|
| `source` | High-Dimensional Statistics |
| `url` | https://ocw.mit.edu/courses/18-s997-high-dimensional-statistics-spring-2015/ |
| `statement_type` | Proposition |
| `statement_number` | 1.1 |
| `statement_name` | Gaussian tail bound (Mills inequality) |
