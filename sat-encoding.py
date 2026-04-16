#!/usr/bin/env python3
from __future__ import annotations

import argparse
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver


def normalize_pair(u: int, v: int) -> tuple[int, int]:
    if u == v:
        raise ValueError("self-loops are not allowed")
    return (u, v) if u < v else (v, u)


@dataclass
class EncodedInstance:
    vertex_count: int
    s: int
    t: int
    cnf: CNF
    edge_vars: dict[tuple[int, int], int]

    def model_edges(self, model: list[int] | None) -> list[tuple[int, int]]:
        if model is None:
            return []
        positive = {lit for lit in model if lit > 0}
        return [
            pair
            for pair, var in sorted(self.edge_vars.items())
            if var in positive
        ]


class DoublySaturatedRamseyEncoder:
    def __init__(
        self,
        vertex_count: int,
        s: int,
        t: int,
        *,
        cardinality_encoding: int = EncType.seqcounter,
        symmetry_breaking: bool = True,
    ) -> None:
        if vertex_count <= 0:
            raise ValueError("vertex_count must be positive")
        if s < 2:
            raise ValueError("s must be at least 2")
        if t < 2:
            raise ValueError("t must be at least 2")

        self.vertex_count = vertex_count
        self.s = s
        self.t = t
        self.cardinality_encoding = cardinality_encoding
        self.symmetry_breaking = symmetry_breaking

        self.vertices = list(range(vertex_count))
        self.cnf = CNF()
        self.vpool = IDPool(start_from=1)
        self.edge_vars: dict[tuple[int, int], int] = {}

        for pair in combinations(self.vertices, 2):
            self.edge_vars[pair] = self.vpool.id(("e", *pair))

    def encode(self) -> EncodedInstance:
        self.add_ramsey_goodness()
        self.add_maximality()
        self.add_minimality()
        if self.symmetry_breaking:
            self.add_lex_symmetry_breaking()
        return EncodedInstance(
            vertex_count=self.vertex_count,
            s=self.s,
            t=self.t,
            cnf=self.cnf,
            edge_vars=self.edge_vars,
        )

    def edge_var(self, u: int, v: int) -> int:
        return self.edge_vars[normalize_pair(u, v)]

    def maximality_witness_var(self, i: int, j: int, k: int) -> int:
        u, v = normalize_pair(i, j)
        if k in (u, v):
            raise ValueError("witness vertex must differ from the base pair")
        return self.vpool.id(("p", u, v, k))

    def minimality_witness_var(self, i: int, j: int, k: int) -> int:
        u, v = normalize_pair(i, j)
        if k in (u, v):
            raise ValueError("witness vertex must differ from the base pair")
        return self.vpool.id(("q", u, v, k))

    def add_ramsey_goodness(self) -> None:
        for clique_vertices in combinations(self.vertices, self.s):
            self.cnf.append(
                [-self.edge_var(u, v) for u, v in combinations(clique_vertices, 2)]
            )

        for indep_vertices in combinations(self.vertices, self.t):
            self.cnf.append(
                [self.edge_var(u, v) for u, v in combinations(indep_vertices, 2)]
            )

    def add_maximality(self) -> None:
        for i, j in combinations(self.vertices, 2):
            witnesses = []
            others = [k for k in self.vertices if k not in (i, j)]

            for k in others:
                witness = self.maximality_witness_var(i, j, k)
                witnesses.append(witness)
                self.cnf.append([-witness, self.edge_var(i, k)])
                self.cnf.append([-witness, self.edge_var(j, k)])

            for k, kp in combinations(others, 2):
                self.cnf.append(
                    [
                        -self.maximality_witness_var(i, j, k),
                        -self.maximality_witness_var(i, j, kp),
                        self.edge_var(k, kp),
                    ]
                )

            self.add_guarded_atleast(self.edge_var(i, j), witnesses, self.s - 2)

    def add_minimality(self) -> None:
        for i, j in combinations(self.vertices, 2):
            witnesses = []
            others = [k for k in self.vertices if k not in (i, j)]

            for k in others:
                witness = self.minimality_witness_var(i, j, k)
                witnesses.append(witness)
                self.cnf.append([-witness, -self.edge_var(i, k)])
                self.cnf.append([-witness, -self.edge_var(j, k)])

            for k, kp in combinations(others, 2):
                self.cnf.append(
                    [
                        -self.minimality_witness_var(i, j, k),
                        -self.minimality_witness_var(i, j, kp),
                        -self.edge_var(k, kp),
                    ]
                )

            self.add_guarded_atleast(-self.edge_var(i, j), witnesses, self.t - 2)

    def add_guarded_atleast(
        self,
        relax_lit: int,
        literals: list[int],
        bound: int,
    ) -> None:
        if bound <= 0:
            return
        if bound > len(literals):
            self.cnf.append([relax_lit])
            return

        card = CardEnc.atleast(
            lits=literals,
            bound=bound,
            encoding=self.cardinality_encoding,
            vpool=self.vpool,
        )
        for clause in card.clauses:
            self.cnf.append([relax_lit, *clause])

    def add_lex_symmetry_breaking(self) -> None:
        for i, j in combinations(self.vertices, 2):
            row_i = [self.edge_var(i, k) for k in self.vertices if k not in (i, j)]
            row_j = [self.edge_var(j, k) for k in self.vertices if k not in (i, j)]
            self.add_lex_leq(row_i, row_j)  

    def add_lex_leq(
        self,
        left: list[int],
        right: list[int],
        maxcomparisons: int | None = None,
    ) -> None:
        if len(left) != len(right):
            raise ValueError("lex vectors must have the same length")
        previous_equal = self.vpool.id()
        self.cnf.append([previous_equal])

        comparisons = 0
        for left_lit, right_lit in zip(left, right):
            if left_lit == right_lit:
                continue

            comparisons += 1
            self.cnf.append([-previous_equal, -left_lit, right_lit])

            next_previous_equal = self.vpool.id()
            self.cnf.append([-next_previous_equal, previous_equal])
            self.cnf.append([-previous_equal, -left_lit, next_previous_equal])
            self.cnf.append([-previous_equal, right_lit, next_previous_equal])
            previous_equal = next_previous_equal

            if maxcomparisons is not None and comparisons >= maxcomparisons:
                break


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Encode doubly saturated R(s,t)-good graphs on n vertices as CNF."
        )
    )
    parser.add_argument("-n", "--vertices", type=int, required=True, help="Number of vertices.")
    parser.add_argument("-s", type=int, required=True, help="Clique parameter.")
    parser.add_argument("-t", type=int, required=True, help="Independence parameter.")

    parser.add_argument(
        "--no-symmetry",
        action="store_true",
        help="Disable the lexicographic symmetry-breaking constraints.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="Optional DIMACS output path.",
    )
    parser.add_argument(
        "--solve",
        action="store_true",
        help="Solve the resulting CNF with PySAT's default backend and print a witness.",
    )
    return parser


def main() -> int:
    args = build_parser().parse_args()

    encoder = DoublySaturatedRamseyEncoder(
        vertex_count=args.vertices,
        s=args.s,
        t=args.t,
        symmetry_breaking=not args.no_symmetry,
        cardinality_encoding=EncType.seqcounter
    )
    instance = encoder.encode()

    print(
        f"n={args.vertices} s={args.s} t={args.t} "
        f"vars={instance.cnf.nv} clauses={len(instance.cnf.clauses)}"
    )

    if args.output is not None:
        instance.cnf.to_file(str(args.output))
        print(f"wrote {args.output}")

    if args.solve:
        with Solver(bootstrap_with=instance.cnf.clauses) as solver:
            satisfiable = solver.solve()
            print("SAT" if satisfiable else "UNSAT")
            if satisfiable:
                edges = instance.model_edges(solver.get_model())
                print(f"edges ({len(edges)}): {edges}")
                adj = {}
                for u, v in edges:
                    adj.setdefault(u, set()).add(v)
                    adj.setdefault(v, set()).add(u)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
