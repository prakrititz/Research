import z3
from .ast import *


def floor_div(a, b):
    """Whole-number division rounding down: Python's ``//``, Coq's ``Z.div`` and Lean's ``Int.fdiv``.

    Z3's own integer ``div`` is Euclidean (the remainder is never negative), which rounds *up*
    when the divisor is negative: 7 div -2 is -3 in Z3 but -4 in Python, Coq and Lean. Without
    this, the prover that searches and the ones that certify (and the emitted program) would
    read the same ``/`` differently. Division by zero stays unspecified, as in Z3: nothing
    proved can depend on its value.
    """
    if z3.is_int_value(b) and b.as_long() > 0:
        return a / b
    return z3.If(b >= 0, a / b, (-a) / (-b))


def divisibility_parts(node):
    """``(x, k)`` when ``node`` is the divisibility test ``x = k * (x / k)`` (in any of its orders), else ``None``.

    Whether ``k`` divides ``x`` does not depend on how the quotient is rounded, so this test keeps
    Z3's native division: the exact rounding-down encoding (a case split on the sign of ``k``)
    made the quantified divisor searches of gcd, is_prime and largest_divisor time out.
    """
    if not (isinstance(node, BinaryOp) and node.op == "="):
        return None
    for x, product in ((node.left, node.right), (node.right, node.left)):
        if not (isinstance(product, BinaryOp) and product.op == "*"):
            continue
        for k, quotient in ((product.left, product.right), (product.right, product.left)):
            if (isinstance(quotient, BinaryOp) and quotient.op == "/"
                    and quotient.left == x and quotient.right == k):
                return x, k
    return None


class Z3Translator:
    def __init__(self):
        self.env = {} # mapping from variable/const name to z3 expression

    def sort_of(self, type_):
        if isinstance(type_, BoolType):
            return z3.BoolSort()
        if isinstance(type_, (IntType, NatType)):
            return z3.IntSort()
        if isinstance(type_, FloatType):
            return z3.RealSort()
        return None

    def array_of(self, name, type_):
        """An array indexed by integers whose elements have the declared sort.

        Every array used to be ``Array(Int, Int)``, so an ``array float`` was reasoned about as if
        it held whole numbers only: a step valid for integers but not for reals (``a < b`` implies
        ``a + 1 <= b``) would have been accepted for a list of floats.
        """
        element = self.sort_of(getattr(type_, "element_type", None))
        return z3.Array(name, z3.IntSort(), z3.IntSort() if element is None else element)

    def declare_params(self, params):
        """Seed the environment with declared parameters (and their primed
        previous-state twins) so that names are given their declared sort."""
        for p in params or []:
            if isinstance(p.type_, ArrayType):
                self.env[p.name] = self.array_of(p.name, p.type_)
                continue
            sort = self.sort_of(p.type_)
            if sort is None:
                continue
            self.env[p.name] = z3.Const(p.name, sort)
            self.env[f"{p.name}0"] = z3.Const(f"{p.name}0", sort)

    def translate(self, node: ASTNode):
        if isinstance(node, Spec):
            # A Spec is a pair of precondition and postcondition
            pre = self.translate(node.precondition)
            post = self.translate(node.postcondition)
            return z3.And(pre, post)
            
        elif isinstance(node, Definition):
            # Translate params into z3 variables and add them to env
            old_env = self.env.copy()
            for p in node.params:
                if isinstance(p.type_, BoolType):
                    self.env[p.name] = z3.Bool(p.name)
                elif isinstance(p.type_, IntType) or isinstance(p.type_, NatType):
                    self.env[p.name] = z3.Int(p.name)
                elif isinstance(p.type_, FloatType):
                    self.env[p.name] = z3.Real(p.name) # Z3 uses Real for float
                elif isinstance(p.type_, ArrayType):
                    self.env[p.name] = self.array_of(p.name, p.type_)
            
            expr = self.translate(node.expr)
            self.env = old_env
            return expr

        elif isinstance(node, QuantifiedExpr):
            old_env = self.env.copy()
            z3_vars = []
            for p in node.params:
                if isinstance(p.type_, BoolType):
                    var = z3.Bool(p.name)
                elif isinstance(p.type_, IntType) or isinstance(p.type_, NatType):
                    var = z3.Int(p.name)
                elif isinstance(p.type_, FloatType):
                    var = z3.Real(p.name)
                else:
                    var = z3.Int(p.name) # Default fallback
                self.env[p.name] = var
                z3_vars.append(var)
                
            body = self.translate(node.expr)
            self.env = old_env
            
            if node.quantifier == 'forall':
                return z3.ForAll(z3_vars, body)
            else:
                return z3.Exists(z3_vars, body)

        elif isinstance(node, BinaryOp):
            parts = divisibility_parts(node)
            if parts is not None:
                x, k = self.translate(parts[0]), self.translate(parts[1])
                if z3.is_int(x) and z3.is_int(k):
                    return x == k * (x / k)                 # native div: divisibility is rounding-free
            l = self.translate(node.left)
            r = self.translate(node.right)
            if node.op == '/\\': return z3.And(l, r)
            if node.op == '\\/': return z3.Or(l, r)
            if node.op == '<': return l < r
            if node.op == '<=': return l <= r
            if node.op == '=': return l == r
            if node.op == '>': return l > r
            if node.op == '>=': return l >= r
            if node.op == '<>': return l != r
            if node.op == '+': return l + r
            if node.op == '-': return l - r
            if node.op == '*': return l * r
            if node.op == '/':
                if z3.is_int(l) and z3.is_int(r):
                    return floor_div(l, r)
                return l / r
            raise ValueError(f"Unsupported binary operator: {node.op!r}")

        elif isinstance(node, UnaryOp):
            e = self.translate(node.expr)
            if node.op == '~': return z3.Not(e)
            if node.op == '-': return -e
            raise ValueError(f"Unsupported unary operator: {node.op!r}")

        elif isinstance(node, Variable) or isinstance(node, Const):
            if node.name in self.env:
                return self.env[node.name]
            # If not in env, create a new uninterpreted constant
            # We assume it's a Real by default if untyped context, but ideally we'd infer types.
            # For this MVP, we create a Real to match float examples.
            var = z3.Real(node.name) 
            self.env[node.name] = var
            return var

        elif isinstance(node, VariablePreviousState):
            var_name = f"{node.name}0"
            if var_name in self.env:
                return self.env[var_name]
            var = z3.Real(var_name)
            self.env[var_name] = var
            return var

        elif isinstance(node, Number):
            if '.' in node.value:
                return z3.RealVal(node.value)
            return z3.IntVal(node.value)

        elif isinstance(node, BooleanConst):
            return z3.BoolVal(node.value)

        elif isinstance(node, ArraySelect):
            arr = self.translate(Variable(node.array)) 
            idx = self.translate(node.index)
            return z3.Select(arr, idx)
            
        elif isinstance(node, ArraySlice):
            raise NotImplementedError("Z3 does not have native Array slice. Requires axioms.")
            
        raise ValueError(f"Unknown AST node type: {type(node)}")
