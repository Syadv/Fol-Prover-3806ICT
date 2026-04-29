"""
Parser for FOL formulae.

Accepts both course-style syntax and ASCII alternatives:

  Atoms:       P, Q, R, ...   (propositions, just 0-ary predicates)
               P(x, a, f(x))  (with terms)
  Constants:   a, b, c, ...   (lowercase starting a-e)
  Variables:   x, y, z, ...   (lowercase starting u-z)
  Functions:   f(t1, ..., tn) (lowercase with parens)
  Connectives: ~A, !A, ¬A
               A & B, A /\\ B
               A | B, A \\/ B
               A -> B, A → B
  Quantifiers: forall x. A, ∀x.A
               exists x. A, ∃x.A
  Constants:   True, T, ⊤
               False, ⊥        (note: F alone is parsed as a predicate name,
                                use False or ⊥ if you want bot)

Precedence (lowest to highest): ->, |, &, ~, quantifiers, atoms.
-> is right-associative, & and | are left-associative.

Example file:
  forall x. (P(x) -> exists y. R(x, y))
  (A -> B) -> ((~A -> B) -> B)
"""
from __future__ import annotations
from formula import *
import re


class ParseError(Exception):
    pass


# Tokeniser

# I list the patterns in order so longer matches (like ->) win over shorter
# overlapping ones. The (?P<name>...) groups let me know which kind of token
# matched.
TOKEN_SPEC = [
    ("FORALL",    r"(?:forall|∀)"),
    ("EXISTS",    r"(?:exists|∃)"),
    ("IMP",       r"(?:->|→)"),
    ("AND",       r"(?:/\\|&|∧)"),
    ("OR",        r"(?:\\/|\||∨)"),
    ("NOT",       r"(?:~|!|¬)"),
    ("TOP",       r"(?:True|⊤)"),
    ("BOT",       r"(?:False|⊥)"),
    ("DOT",       r"\."),
    ("COMMA",     r","),
    ("LPAREN",    r"\("),
    ("RPAREN",    r"\)"),
    ("TURNSTILE", r"(?:⊢|\\?⊢|:-)"),
    ("NAME",      r"[A-Za-z_][A-Za-z0-9_]*"),
    ("SKIP",      r"[ \t]+"),
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


# Recursive descent parser
# Standard textbook style. One method per precedence level.

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
            raise ParseError(f"ran out of input, expected {expected_kind}")
        if expected_kind and tok[0] != expected_kind:
            raise ParseError(f"expected {expected_kind}, got {tok}")
        self.pos += 1
        return tok

    def at_end(self) -> bool:
        return self.pos >= len(self.tokens)

    def parse_formula(self) -> Formula:
        return self.parse_imp()

    def parse_imp(self) -> Formula:
        # right-associative: A -> B -> C parses as A -> (B -> C)
        left = self.parse_or()
        if self.peek() and self.peek()[0] == "IMP":
            self.consume("IMP")
            right = self.parse_imp()
            return Imp(left, right)
        return left

    def parse_or(self) -> Formula:
        left = self.parse_and()
        while self.peek() and self.peek()[0] == "OR":
            self.consume("OR")
            right = self.parse_and()
            left = Or(left, right)
        return left

    def parse_and(self) -> Formula:
        left = self.parse_unary()
        while self.peek() and self.peek()[0] == "AND":
            self.consume("AND")
            right = self.parse_unary()
            left = And(left, right)
        return left

    def parse_unary(self) -> Formula:
        # ~ binds tighter than & and |, so it's at the unary level
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
        self.consume()  # forall or exists token
        var_tok = self.consume("NAME")
        var_name = var_tok[1]
        self.consume("DOT")
        # the body of the quantifier binds tightly - "forall x. A & B"
        # means forall x. (A & B) since the body is parsed as one unary
        body = self.parse_unary()
        return cls(var_name, body)

    def parse_atom(self) -> Formula:
        tok = self.peek()
        if tok is None:
            raise ParseError("ran out of input in atom")

        if tok[0] == "TOP":
            self.consume()
            return Top()
        if tok[0] == "BOT":
            self.consume()
            return Bot()

        # parenthesised expression
        if tok[0] == "LPAREN":
            self.consume("LPAREN")
            f = self.parse_formula()
            self.consume("RPAREN")
            return f

        # name = either a predicate (with or without args) or a quantifier
        # already handled above
        if tok[0] == "NAME":
            name = self.consume("NAME")[1]
            if self.peek() and self.peek()[0] == "LPAREN":
                # predicate with arguments
                self.consume("LPAREN")
                args = self.parse_term_list()
                self.consume("RPAREN")
                return Pred(name, tuple(args))
            else:
                # 0-ary predicate
                return Pred(name)
        raise ParseError(f"unexpected token in atom: {tok}")

    def parse_term_list(self) -> list[Term]:
        terms = [self.parse_term()]
        while self.peek() and self.peek()[0] == "COMMA":
            self.consume("COMMA")
            terms.append(self.parse_term())
        return terms

    def parse_term(self) -> Term:
        tok = self.peek()
        if tok is None:
            raise ParseError("ran out of input in term")
        if tok[0] != "NAME":
            raise ParseError(f"expected name in term, got {tok}")

        name = self.consume("NAME")[1]
        # function application?
        if self.peek() and self.peek()[0] == "LPAREN":
            self.consume("LPAREN")
            args = self.parse_term_list()
            self.consume("RPAREN")
            return Fun(name, tuple(args))

        # heuristic: if it starts with u-z it's a variable, otherwise a constant
        # this works because in the textbook conventions, x/y/z are variables
        # and a/b/c are constants. quantifier binding context can override
        # this when needed.
        if name[0].islower() and name[0] in "uvwxyz":
            return Var(name)
        else:
            return Const(name)


def parse_formula(text: str) -> Formula:
    """Parse a single formula from a string."""
    tokens = tokenise(text.strip())
    if not tokens:
        raise ParseError("nothing to parse")
    parser = Parser(tokens)
    f = parser.parse_formula()
    if not parser.at_end():
        raise ParseError(f"junk left over after formula: {parser.tokens[parser.pos:]}")
    return f


def parse_file(filename: str) -> list[Formula]:
    """One formula per line. Blank lines and # comments get skipped."""
    formulae = []
    with open(filename, "r") as fp:
        for line_no, line in enumerate(fp, 1):
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            try:
                formulae.append(parse_formula(line))
            except ParseError as e:
                # don't crash the whole file just because one line is broken
                print(f"Parse error on line {line_no}: {e}")
                print(f"  Line: {line}")
    return formulae


# quick check
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
