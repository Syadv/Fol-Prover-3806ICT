"""
Parser for first-order logic formulae.

Accepted syntax (one formula per line):
  Atoms:       P, Q, R, ...             (propositions — 0-ary predicates)
               P(x, a, f(x))           (predicates with terms)
  Constants:   a, b, c, ...            (lowercase single letters or names starting with a-e)
  Variables:   x, y, z, ...            (lowercase names starting with u-z)
  Functions:   f(t1, ..., tn)          (lowercase names with parens)
  Connectives: ~A  or  ¬A  or  !A      (negation)
               A /\\ B  or  A & B       (conjunction)
               A \\/ B  or  A | B       (disjunction)
               A -> B  or  A → B       (implication)
  Quantifiers: forall x. A  or  ∀x.A   (universal)
               exists x. A  or  ∃x.A   (existential)
  Constants:   True / T / ⊤            (top)
               False / F / ⊥           (bottom — careful, F alone is a pred)
  Parens:      (A)

Precedence (low to high): →, ∨, ∧, ¬, quantifiers, atoms
→ is right-associative; ∧ and ∨ are left-associative.

Example input file:
  forall x. (P(x) -> exists y. R(x, y))
  (A -> B) -> ((~A -> B) -> B)
"""
from __future__ import annotations
from formula import *
import re


class ParseError(Exception):
    pass


# ── Tokeniser ────────────────────────────────────────────────────────

TOKEN_SPEC = [
    ("FORALL",  r"(?:forall|∀)"),
    ("EXISTS",  r"(?:exists|∃)"),
    ("IMP",     r"(?:->|→)"),
    ("AND",     r"(?:/\\|&|∧)"),
    ("OR",      r"(?:\\/|\||∨)"),
    ("NOT",     r"(?:~|!|¬)"),
    ("TOP",     r"(?:True|⊤)"),
    ("BOT",     r"(?:False|⊥)"),
    ("DOT",     r"\."),
    ("COMMA",   r","),
    ("LPAREN",  r"\("),
    ("RPAREN",  r"\)"),
    ("TURNSTILE", r"(?:⊢|\\?⊢|:-)"),
    ("NAME",    r"[A-Za-z_][A-Za-z0-9_]*"),
    ("SKIP",    r"[ \t]+"),
]

_token_re = re.compile("|".join(f"(?P<{name}>{pattern})" for name, pattern in TOKEN_SPEC))


def tokenise(text: str) -> list[tuple[str, str]]:
    tokens = []
    for m in _token_re.finditer(text):
        kind = m.lastgroup
        value = m.group()
        if kind == "SKIP":
            continue
        tokens.append((kind, value))
    return tokens


# ── Recursive descent parser ────────────────────────────────────────

class Parser:
    def __init__(self, tokens: list[tuple[str, str]]):
        self.tokens = tokens
        self.pos = 0

    def peek(self) -> tuple[str, str] | None:
        if self.pos < len(self.tokens):
            return self.tokens[self.pos]
        return None

    def consume(self, expected_kind: str | None = None) -> tuple[str, str]:
        tok = self.peek()
        if tok is None:
            raise ParseError(f"Unexpected end of input, expected {expected_kind}")
        if expected_kind and tok[0] != expected_kind:
            raise ParseError(f"Expected {expected_kind}, got {tok}")
        self.pos += 1
        return tok

    def at_end(self) -> bool:
        return self.pos >= len(self.tokens)

    # formula ::= imp_expr
    def parse_formula(self) -> Formula:
        return self.parse_imp()

    # imp_expr ::= or_expr ( '->' imp_expr )?    (right-assoc)
    def parse_imp(self) -> Formula:
        left = self.parse_or()
        if self.peek() and self.peek()[0] == "IMP":
            self.consume("IMP")
            right = self.parse_imp()  # right-associative
            return Imp(left, right)
        return left

    # or_expr ::= and_expr ( '\\/' and_expr )*
    def parse_or(self) -> Formula:
        left = self.parse_and()
        while self.peek() and self.peek()[0] == "OR":
            self.consume("OR")
            right = self.parse_and()
            left = Or(left, right)
        return left

    # and_expr ::= unary ( '/\\' unary )*
    def parse_and(self) -> Formula:
        left = self.parse_unary()
        while self.peek() and self.peek()[0] == "AND":
            self.consume("AND")
            right = self.parse_unary()
            left = And(left, right)
        return left

    # unary ::= '~' unary | quantifier | atom
    def parse_unary(self) -> Formula:
        tok = self.peek()
        if tok and tok[0] == "NOT":
            self.consume("NOT")
            sub = self.parse_unary()
            return Not(sub)
        if tok and tok[0] == "FORALL":
            return self.parse_quantifier(Forall)
        if tok and tok[0] == "EXISTS":
            return self.parse_quantifier(Exists)
        return self.parse_atom()

    def parse_quantifier(self, cls):
        self.consume()  # consume FORALL/EXISTS
        var_tok = self.consume("NAME")
        var_name = var_tok[1]
        self.consume("DOT")
        body = self.parse_unary()  # quantifier binds tightly
        return cls(var_name, body)

    # atom ::= TOP | BOT | NAME ( '(' term_list ')' )? | '(' formula ')'
    def parse_atom(self) -> Formula:
        tok = self.peek()
        if tok is None:
            raise ParseError("Unexpected end of input in atom")

        if tok[0] == "TOP":
            self.consume()
            return Top()
        if tok[0] == "BOT":
            self.consume()
            return Bot()

        if tok[0] == "LPAREN":
            self.consume("LPAREN")
            f = self.parse_formula()
            self.consume("RPAREN")
            return f

        if tok[0] == "NAME":
            name = self.consume("NAME")[1]
            # Check if it's a predicate/function with arguments
            if self.peek() and self.peek()[0] == "LPAREN":
                self.consume("LPAREN")
                args = self.parse_term_list()
                self.consume("RPAREN")
                return Pred(name, tuple(args))
            else:
                # 0-ary predicate (proposition)
                return Pred(name)
        raise ParseError(f"Unexpected token in atom: {tok}")

    def parse_term_list(self) -> list[Term]:
        terms = [self.parse_term()]
        while self.peek() and self.peek()[0] == "COMMA":
            self.consume("COMMA")
            terms.append(self.parse_term())
        return terms

    def parse_term(self) -> Term:
        tok = self.peek()
        if tok is None:
            raise ParseError("Unexpected end of input in term")
        if tok[0] != "NAME":
            raise ParseError(f"Expected name in term, got {tok}")

        name = self.consume("NAME")[1]
        # Check for function application
        if self.peek() and self.peek()[0] == "LPAREN":
            self.consume("LPAREN")
            args = self.parse_term_list()
            self.consume("RPAREN")
            return Fun(name, tuple(args))

        # Heuristic: uppercase or single letter a-e => const; u-z => variable
        # This can be overridden by context (quantifier binding)
        if name[0].islower() and name[0] in "uvwxyz":
            return Var(name)
        else:
            return Const(name)


def parse_formula(text: str) -> Formula:
    """Parse a single formula from text."""
    tokens = tokenise(text.strip())
    if not tokens:
        raise ParseError("Empty formula")
    parser = Parser(tokens)
    f = parser.parse_formula()
    if not parser.at_end():
        raise ParseError(f"Unexpected tokens after formula: {parser.tokens[parser.pos:]}")
    return f


def parse_file(filename: str) -> list[Formula]:
    """Parse a file with one formula per line. Blank lines and # comments are skipped."""
    formulae = []
    with open(filename, "r") as fp:
        for line_no, line in enumerate(fp, 1):
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            try:
                formulae.append(parse_formula(line))
            except ParseError as e:
                print(f"Parse error on line {line_no}: {e}")
                print(f"  Line: {line}")
    return formulae


# ── Quick test ───────────────────────────────────────────────────────

if __name__ == "__main__":
    tests = [
        "A",
        "A & B",
        "A | B",
        "A -> B",
        "~A",
        "(A -> B) -> ((~A -> B) -> B)",
        "forall x. P(x)",
        "exists x. (P(x) & Q(x))",
        "forall x. (P(x) -> exists y. R(x, y))",
        "forall x. P(x) -> exists y. R(x, y)",
        "~(forall x. P(x)) -> exists x. ~P(x)",
    ]
    for t in tests:
        try:
            f = parse_formula(t)
            print(f"  {t:50s}  =>  {f}")
        except ParseError as e:
            print(f"  {t:50s}  =>  ERROR: {e}")
