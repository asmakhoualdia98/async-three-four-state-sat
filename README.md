# Satisfiability Meets Self-Stabilization

## 🧩 Overview

This project is a Python-based SAT encoding framework for modeling and analyzing the self-stabilization properties of **Dijkstra’s asynchronous token circulation**, with a primary focus on Dijkstra’s **three-state and four-state algorithms**.

The framework generates benchmark instances in CNF format for formal verification and experimental evaluation using SAT solvers. It supports the encoding of convergence and divergence behaviors under multiple daemon assumptions.

Two variants of the algorithm are considered:

* **Four-State**: Dijkstra’s algorithm with four possible states.
* **Three-State**: Dijkstra’s algorithm with three possible states.

---

## 🚀 Features

* ✅ Three-State and Four-State models
* 🔁 Behavior analysis: `CONV` (converging) and `DIV` (diverging)
* ⚙️ Daemon assumptions: `SYNC`, `CEN`, `LOC`, `DIS-UNFAIR`
* 🛠 Generates CNF files encoding Dijkstra’s algorithm behavioral properties
* 📦 Provides a collection of generated SAT benchmark instances

---

## 📦 Installation & Usage (Generate a Single CNF Instance)

```bash
git clone <repository-url>
cd <repository-directory>
pip install python-sat[pblib,aiger]
```

### Four-State

```bash
python3 GraphSolver_FourState.py <num_nodes> <CONV|DIV> <SYNC|CEN|LOC|DIS-UNFAIR>
```

### Three-State

```bash
python3 GraphSolver_ThreeState.py <num_nodes> <CONV|DIV> <SYNC|CEN|LOC|DIS-UNFAIR>
```


---

## 📊 Benchmark Instances

The provided benchmarks consider ring sizes:

```text
n = 3, 4, 5, 6, 7, 8, 9, 10
```

For each ring size, the framework generates instances for:

* 2 behaviors: `CONV`, `DIV`
* 4 daemon assumptions: `SYNC`, `CEN`, `LOC`, `DIS-UNFAIR`

---

## 📚 References

📄 Asma Khoualdia, Sami Cherif, Stéphane Devismes, Léo Robert. Satisfiability Meets Self-Stabilization. International Symposium on Stabilization, Safety, and Security of Distributed Systems (SSS 2026), October 2026, Gothenburg, Sweden.

---

You can refer to our previous work on synchronous unison, which provides both source code and benchmark instances:

📄 Asma Khoualdia, Sami Cherif, Stéphane Devismes, Léo Robert. Analyzing Self-Stabilization of Synchronous Unison via Propositional Satisfiability. International Conference on Principles and Practice of Constraint Programming (CP 2025), Glasgow, Scotland. [DOI: https://doi.org/10.4230/LIPIcs.CP.2025.19/](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CP.2025.19)

📄 Asma Khoualdia, Sami Cherif, Stéphane Devismes, Léo Robert. On the Self-Stabilization of Dijkstra’s Asynchronous Token Circulation. International Conference on Principles and Practice of Constraint Programming (CP 2026), July 2026, Lisbon, Portugal. https://doi.org/10.4230/LIPIcs.CP.2026.32
