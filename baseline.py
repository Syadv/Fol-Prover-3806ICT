"""
First attempt at Algorithm 2 from Hou's textbook (page 67).
Just doing propositional logic for now — will add quantifiers later.
"""
import time

# Formulae represented as nested tuples:
#   ('atom', 'A')           -> atom A
#   ('not', F)              -> ~F
#   ('and', F, G)           -> F & G
#   ('or', F, G)            -> F | G
#   ('imp', F, G)           -> F -> G
#   ('top',)                -> True
#   ('bot',)                -> False


def is_closed(gamma, delta):
    # id rule: same formula on both sides
    for f in gamma:
        if f in delta:
            return True
    # top R: ('top',) on right
    if ('top',) in delta:
        return True
    # bot L: ('bot',) on left
    if ('bot',) in gamma:
        return True
    return False


def prove(gamma, delta, depth=0):
    if depth > 100:
        return False  # give up

    if is_closed(gamma, delta):
        return True

    # ── non-branching rules ──
    # and L:  G, A&B |- D  =>  G, A, B |- D
    for i, f in enumerate(gamma):
        if f[0] == 'and':
            new_gamma = gamma[:i] + gamma[i+1:] + [f[1], f[2]]
            return prove(new_gamma, delta, depth+1)

    # or R:  G |- A|B, D  =>  G |- A, B, D
    for i, f in enumerate(delta):
        if f[0] == 'or':
            new_delta = delta[:i] + delta[i+1:] + [f[1], f[2]]
            return prove(gamma, new_delta, depth+1)

    # imp R:  G |- A->B, D  =>  G, A |- B, D
    for i, f in enumerate(delta):
        if f[0] == 'imp':
            new_gamma = gamma + [f[1]]
            new_delta = delta[:i] + delta[i+1:] + [f[2]]
            return prove(new_gamma, new_delta, depth+1)

    # not L:  G, ~A |- D  =>  G |- A, D
    for i, f in enumerate(gamma):
        if f[0] == 'not':
            new_gamma = gamma[:i] + gamma[i+1:]
            new_delta = delta + [f[1]]
            return prove(new_gamma, new_delta, depth+1)

    # not R:  G |- ~A, D  =>  G, A |- D
    for i, f in enumerate(delta):
        if f[0] == 'not':
            new_gamma = gamma + [f[1]]
            new_delta = delta[:i] + delta[i+1:]
            return prove(new_gamma, new_delta, depth+1)

    # ── branching rules ──
    # and R: G |- A&B, D  =>  G |- A, D  AND  G |- B, D
    for i, f in enumerate(delta):
        if f[0] == 'and':
            d1 = delta[:i] + delta[i+1:] + [f[1]]
            d2 = delta[:i] + delta[i+1:] + [f[2]]
            return prove(gamma, d1, depth+1) and prove(gamma, d2, depth+1)

    # or L: G, A|B |- D  =>  G, A |- D  AND  G, B |- D
    for i, f in enumerate(gamma):
        if f[0] == 'or':
            g1 = gamma[:i] + gamma[i+1:] + [f[1]]
            g2 = gamma[:i] + gamma[i+1:] + [f[2]]
            return prove(g1, delta, depth+1) and prove(g2, delta, depth+1)

    # imp L: G, A->B |- D  =>  G |- A, D  AND  G, B |- D
    for i, f in enumerate(gamma):
        if f[0] == 'imp':
            new_gamma = gamma[:i] + gamma[i+1:]
            d1 = delta + [f[1]]
            g2 = new_gamma + [f[2]]
            return prove(new_gamma, d1, depth+1) and prove(g2, delta, depth+1)

    # TODO: add forall L, exists R, forall R, exists L for FOL support
    return False


if __name__ == "__main__":
    A = ('atom', 'A')
    B = ('atom', 'B')
    C = ('atom', 'C')

    tests = [
        ("A -> A", ('imp', A, A), True),
        ("A & B -> B & A", ('imp', ('and', A, B), ('and', B, A)), True),
        ("(A -> B) -> ((~A -> B) -> B)",
         ('imp', ('imp', A, B), ('imp', ('imp', ('not', A), B), B)), True),
        ("A | ~A", ('or', A, ('not', A)), True),
        ("~~A -> A", ('imp', ('not', ('not', A)), A), True),
        ("A -> B", ('imp', A, B), False),
        ("A & B", ('and', A, B), False),
    ]

    for name, f, expected in tests:
        result = prove([], [f])
        status = "OK" if result == expected else "FAIL"
        print(f"  [{status}] {name}: got {result}, expected {expected}")
