# Gluon-Formalization-Coq

Formal verification of the [Gluon protocol](https://gluon.network) — a stablecoin system — using the [Rocq Prover](https://rocq-prover.org) (formerly Coq) interactive theorem prover.

## Overview

This project formalizes the core correctness properties of the Gluon stablecoin protocol. It defines the protocol's state machine, reaction functions (fission, fusion, beta decay), and fee mechanisms, then proves key theorems about their behavior.

### Source Files

| File | Description |
|------|-------------|
| `Formalization/HelperFunctions.v` | Utility functions (`extract_value`, boolean comparisons over `R`) |
| `Formalization/Datatypes.v` | Core types: `ReactorState`, `StableCoinState`, `State`, `Trace`, `Event`, etc. |
| `Formalization/Functions.v` | Protocol functions: pricing, fees, fission/fusion/beta-decay reactions, state transitions |
| `Formalization/HelperLemmas.v` | Auxiliary lemmas used across proofs |
| `Formalization/FunctionProofs.v` | Correctness proofs for individual functions |
| `Formalization/CustomTactics.v` | Custom Rocq tactics |
| `Formalization/Theorem1.v` | `peg_maintenance_upper_bound` |
| `Formalization/Theorem2.v` | `peg_maintenance_lower_bound` |
| `Formalization/Theorem3.v` | `peg_robustness_during_market_crashes` |
| `Formalization/Theorem4.v` | `insolvency` (protocol solvency guarantee) |
| `Formalization/Theorem5.v` | `insolvency` under depeg conditions |

## Prerequisites

- **Rocq Prover 9.1.0** — [rocq-prover.org/install](https://rocq-prover.org/install)
- **make**

## Compiling

First, ensure the opam environment is active:

```bash
eval $(opam env)
```

Then build all `.v` files:

```bash
make
```

This runs `rocq makefile` to generate `Makefile.coq` from `_CoqProject`, then compiles all source files in dependency order into `.vo` object files.

To clean compiled artifacts:

```bash
make clean
```

## Interactive Exploration with VsRocq

[VsRocq](https://github.com/rocq-prover/vscoq) provides an interactive proof assistant inside VS Code, letting you step through proofs line by line and inspect the proof state at each point.

### Setup

1. Install **VsRocq 2.3.4** — see the [VsRocq installation guide](https://github.com/rocq-prover/vscoq?tab=readme-ov-file#installation--setup).

2. In VS Code settings, point `vscoq.path` to your `vscoqtop` binary:

```json
"vscoq.path": "/path/to/vscoqtop"
```

You can find the path with:

```bash
which vscoqtop
```

### Usage

Open any `.v` file in VS Code. The proof state panel appears on the right showing current **goals** and **context** at the cursor position.

| Action | Keybinding |
|--------|------------|
| Step forward one sentence | `Alt+Down` |
| Step backward one sentence | `Alt+Up` |
| Go to cursor position | `Alt+Right` |
| Interrupt / reset | `Alt+C` |

### Project Root

Open the project from its root directory (the folder containing `_CoqProject`) so that VsRocq correctly resolves the `StableCoinFormalization` logical path:

```bash
code /path/to/Gluon-Formalization-Coq
```
