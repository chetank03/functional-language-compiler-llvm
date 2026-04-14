# Functional Language Compiler to LLVM-IR

This repository contains a Scala-based compiler project for a small functional programming language that targets LLVM-IR. The project was originally developed as part of compiler coursework at King's College London and is presented here as a portfolio project because it demonstrates core compiler construction work: lexing, parsing-oriented language design, typed language extensions, and code generation.

## Overview

The compiler translates `.fun` source programs into LLVM `.ll` output. The implementation includes:

- derivative-based lexical analysis using regular-expression derivatives
- token extraction with recorded captures for identifiers, keywords, literals, and operators
- support for typed language constructs and user-defined functions
- code generation to LLVM-IR
- sample programs covering recursion, arithmetic, and Mandelbrot-style workloads

The main implementation lives in [`cw5/cw05.sc`](./cw5/cw05.sc).

## Key Features

- **Custom lexer implementation**
  The project builds a lexer from regular expression derivatives rather than relying on a generator tool. It supports recorded groups, nullable checks, derivatives, simplification, token reconstruction, and environment extraction.

- **Language-level extensions**
  The language supports typed values and function-oriented constructs in addition to keywords, identifiers, operators, strings, comments, numeric literals, and character constants.

- **LLVM-IR output**
  Source programs are compiled into LLVM `.ll` files, making the project a full compilation pipeline rather than a parser-only assignment.

- **Representative test programs**
  The repository includes recursive and computation-heavy examples such as factorial, Towers of Hanoi, and Mandelbrot-style programs.

## Repository Layout

```text
cw5/
  cw05.sc     Main Scala implementation
  fact.fun    Example source program
  fact.ll     Generated LLVM-IR output
  hanoi.fun   Example source program
  hanoi.ll    Generated LLVM-IR output
  mand.fun    Example source program
  mand.ll     Generated LLVM-IR output
  mand2.fun   Example source program
  mand2.ll    Generated LLVM-IR output
  sqr.fun     Example source program
  sqr.ll      Generated LLVM-IR output
```

## What This Project Demonstrates

- compiler implementation in Scala
- lexer construction from first principles
- typed language handling and syntax extension
- transformation from high-level source programs to LLVM intermediate representation
- work on nontrivial examples involving recursion and mathematical computation

## Sample Programs

- `fact.fun`: factorial example
- `hanoi.fun`: recursive Towers of Hanoi program
- `mand.fun` and `mand2.fun`: Mandelbrot-style benchmark programs
- `sqr.fun`: simple arithmetic example

Each sample has a corresponding `.ll` file showing the generated LLVM-IR output.

## Notes

- This repository is a cleaned public version of an academic project.
- The original coursework prompt referenced in the initial repository has been preserved for context, but this README focuses on the implemented compiler work itself.
