"""Exact certificate for the entire five-level slice in the research note.

All computations in the verifier use Python's standard library and rational
arithmetic. No numerical optimizer or eigensolver is needed for replay.
"""
from fractions import Fraction as Q
from itertools import permutations


def determinant(matrix):
    n = len(matrix)
    total = Q(0)
    for order in permutations(range(n)):
        inversions = sum(order[i] > order[j] for i in range(n) for j in range(i + 1, n))
        term = (-1) ** inversions
        for i, j in enumerate(order):
            term *= matrix[i][j]
        total += term
    return total


def certificate():
    d = [Q(i, 5) for i in range(1, 6)]
    p = [Q(i, 16) for i in (6, 5, 5, 8, 8)]
    y = [Q(i, 10**6) for i in (3878, 4479, 3695, -9419, -107404)]
    target_probability = Q(7, 100)
    target = target_probability * sum(value**2 for value in d)
    t2, t6, t10 = (sum(pi * di**k for pi, di in zip(p, d)) for k in (2, 6, 10))
    constant = (t2 - target) * t10**2 - t10 * t6**2

    # G = B H B-transpose, where the first four rows of B form I and
    # the last row is (-1,-1,-1,-1). These differences are B-transpose times d^k.
    u = [d[i]**10 - d[4]**10 for i in range(4)]
    v = [d[i]**6 - d[4]**6 for i in range(4)]
    objective = [
        [
            -(t2 - target) * u[i] * u[j] + t6 * (u[i] * v[j] + v[i] * u[j])
            - t10 * v[i] * v[j]
            for j in range(4)
        ]
        for i in range(4)
    ]
    slack = [
        [(y[i] if i == j else 0) + y[4] - objective[i][j] for j in range(4)]
        for i in range(4)
    ]
    minors = [determinant([row[:k] for row in slack[:k]]) for k in range(1, 5)]
    upper = constant + sum(yi * pi**2 for yi, pi in zip(y, p))
    assert all(minor > 0 for minor in minors)
    assert upper < 0
    return minors, upper


if __name__ == "__main__":
    minors, upper = certificate()
    print("Leading principal minors of dual slack:", *(str(m) for m in minors), sep="\n")
    print("Exact upper bound for 4(N - K J10):", upper)
    print("Every frame in this fixed spectrum and diagonal slice has probability < 7/100.")
