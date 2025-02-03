from sage.arith.functions import lcm
from sage.arith.misc import gcd
from sage.misc.latex import latex, LatexExpr
from sage.rings.infinity import infinity
from sage.rings.integer import Integer
from sage.rings.number_field.number_field_base import NumberField
from sage.rings.qqbar import AA
from sage.rings.rational_field import Q
from sage.rings.real_mpfr import RealField
from sage.rings.ring import Ring
from sage.structure.element import FieldElement
from sage.structure.richcmp import richcmp, op_EQ, op_GE, op_GT, op_LE, op_LT, op_NE
from sage.symbolic.ring import SR


class IncompleteSqrtExtensionElement(FieldElement):
    def __init__(self, parent, u, v=Integer(1)):
        super().__init__(parent)
        base_ring = parent.base_ring()
        if isinstance(v, IncompleteSqrtExtensionElement):
            assert v.v.is_one()
            v = v.u / v.d
        if isinstance(u, IncompleteSqrtExtensionElement):
            v = u.v * v
            u = u.u / u.d
        u = base_ring(u)
        v = base_ring(v)
        self._pretty = False
        if u.is_zero() or v.is_zero():
            u = v = base_ring.zero()
            self._pretty = True
        elif v.is_square():
            u = u * v.sqrt()
            v = base_ring.one()
        self.u = u
        self.v = v
        self.d = Integer(1)

    def _prettify(self):
        if self._pretty:
            return
        u = self.u
        v = self.v
        if v.is_rational():
            a = lcm(w.denom() for w in v)
            a *= a.squarefree_part()
            u = u / a.sqrt()
            v = v * a
            b = gcd(iter(v))
            b /= b.squarefree_part()
            u = u * b.sqrt()
            v = v / b
        self.d = lcm(w.denom() for w in u)
        self.u = u * self.d
        self.v = v
        self._pretty = True

    def _repr_(self):
        self._prettify()
        d = "" if self.d.is_one() else f"/{self.d}"
        u = self.u if sum(w != 0 for w in self.u) == 1 else f"({self.u})"
        if self.v.is_one() or self.v.is_zero():
            return f"{u}{d}"
        elif self.u.is_one() and self.d.is_one():
            return f"sqrt({self.v})"
        elif (-self.u).is_one() and self.d.is_one():
            return f"-sqrt({self.v})"
        return f"{u}{d} * sqrt({self.v})"

    def _latex_(self):
        self._prettify()
        u = latex(self.u)
        v = latex(self.v)
        d = latex(self.d)
        if self.d.is_one():
            if self.v.is_one() or self.v.is_zero():
                return u
            elif self.u.is_one():
                return LatexExpr(r"\sqrt{%s}" % v)
            elif (-self.u).is_one():
                return LatexExpr(r"-\sqrt{%s}" % v)
            if sum(w != 0 for w in self.u) > 1:
                u = r"\left(%s\right)" % u
        else:
            if sum(w != 0 for w in self.u) > 1 or \
                    next(x for x in self.u if not x.is_zero()) > 0:
                u = r"\frac{%s}{%s}" % (u, d)
            else:
                u = r"-\frac{%s}{%s}" % (latex(-self.u), d)
            if self.v.is_one() or self.v.is_zero():
                return LatexExpr(u)
        return LatexExpr(r"%s \cdot \sqrt{%s}" % (u, v))

    def _algebraic_(self, ring):
        return ring(self.u / self.d) * ring(self.v).sqrt()

    def _rational_(self, ring=Q):
        return ring(AA(self))

    def _symbolic_(self, ring=SR):
        return self._algebraic_(ring)._sympy_().simplify()._sage_()

    _integer_ = _real_double_ = _complex_double_ = _rational_

    def numerical_approx(self, digits=53, algorithm=None):
        return RealField(digits)(AA(self))

    def _add_(self, other):
        parent = self.parent()
        if self.is_zero():
            return other
        elif other.is_zero():
            return self
        if self.v == other.v:
            u = other.u
        else:
            v = other.v / self.v
            assert v.is_square()
            u = other.u * v.sqrt()
        return IncompleteSqrtExtensionElement(parent, self.u / self.d + u / other.d, self.v)

    def _mul_(self, other):
        parent = self.parent()
        u = self.u * other.u / (self.d * other.d)
        if self.v == other.v:
            u *= self.v
            v = parent.base_ring().one()
        else:
            v = self.v * other.v
        return IncompleteSqrtExtensionElement(parent, u, v)

    def _neg_(self):
        return IncompleteSqrtExtensionElement(self.parent(), -self.u / self.d, self.v)

    def _pow_(self, other):
        if other.v.is_one() and other.u.is_rational():
            u = Q(other.u / other.d)
            num = u.numerator()
            den = u.denominator()
            if den.is_one():
                return IncompleteSqrtExtensionElement(self.parent(), ((self.u / self.d) ** num) * (self.v ** (num // 2)), self.v ** (num % 2))
            if den == 2 and self.v.is_one():
                return IncompleteSqrtExtensionElement(self.parent(), (self.u / self.d) ** ((num-1) / 2), self.u / self.d)
        raise NotImplementedError

    def __invert__(self):
        return IncompleteSqrtExtensionElement(self.parent(), self.d / (self.u * self.v), self.v)

    def __abs__(self):
        return self if self >= 0 else -self

    def _signed_square(self):
        return self.u.sign() * (self.u / self.d) ** 2 * self.v

    def _richcmp_(self, other, op):
        return richcmp(self._signed_square(), other._signed_square(), op)

    def additive_order(self):
        return Integer(1) if self.is_zero() else infinity

    def sqrt(self):
        assert self.v.is_one() or self.u.is_zero()
        assert self.u >= 0
        parent = self.parent()
        return IncompleteSqrtExtensionElement(parent, parent.base_ring().one(), self.u / self.d)

    
class IncompleteSqrtExtension(NumberField):
    Element = IncompleteSqrtExtensionElement

    def _element_constructor_(self, u, v=None):
        u = self.element_class(self, u)
        if v is not None:
            u = u * self.element_class(self, v)**-1
        return u
    
    def _coerce_map_from_(self, R):
        if isinstance(R, Ring):
            return R.is_subring(self.base_ring())
        else:
            return isinstance(R, int)

    def gen(self, n=0):
        if n == 0:
            return self.one()
        else:
            raise IndexError("n must be 0")

    def gens(self):
        return (self.one(), )

    def ngens(self):
        return 1
