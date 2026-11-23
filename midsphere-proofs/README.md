# Proof scripts for "Eleven theorems on the tetrahedron with a midsphere"

These are the computer parts of the proofs in the paper. Everything is exact: no floating point is used in any step that the proofs rely on.

Requirements: Python 3 with SymPy, and [Singular](https://www.singular.uni-kl.de/) for the Gröbner basis in `C1/`.

## `independent/`: Theorems 1–10

Run these from inside `independent/`.

| Command | What it does | Time |
|---|---|---|
| `python3 symbolic_check.py` | Proves Theorems 1–10 as identities of rational functions in Q(t1, t2, t3) with t0 = 1. Theorems that involve the Soddy spheres are computed in the quadratic extension Q(t1, t2, t3)(√D). The output is in `symbolic_check.log`. | about 3 min |
| `python3 symbolic_check.py 1 4 8` | Runs only the listed theorems. | |
| `python3 exact_check.py [N]` | Checks Theorems 1–10 exactly on N random rational tangent lengths. This is an independent check, not a proof. | |
| `python3 controls.py` | Control runs: one point in each statement is replaced by a nearby point, and every control must fail. | |

## `C1/`: Theorem 11 (the Fermat line)

Run these from inside `C1/`.

| Command | What it does |
|---|---|
| `Singular c1_ideal.sing` | Computes the ideal membership A·D_d·h_1 ∈ (g_1, …, g_4) and writes the certificate to `c1_cert.txt`. |
| `python3 c1_verify_cert.py` | Checks the certificate independently in SymPy by expanding both sides. The residual must be 0. |
| `python3 c1_lemma.py` | Proves the identity used in the proof of Lemma 9.1 (the line FF\*). |

`c1_cert.txt` is included, so `c1_verify_cert.py` can be run without Singular.

The source comments are in Chinese. The scripts were developed in the author's working directory `code/四面体/circ_scan/proofs/`, and this directory is a copy of them.
