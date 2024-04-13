from sage.misc.latex import latex, LatexExpr
from sage.rings.integer import Integer
from sage.rings.number_field.number_field_base import NumberField
from sage.rings.qqbar import AA
from sage.rings.rational_field import Q
from sage.rings.real_mpfr import RealField
from sage.rings.ring import Ring
from sage.structure.element import FieldElement
from sage.structure.richcmp import richcmp, op_EQ, op_GE, op_GT, op_LE, op_LT, op_NE


class IncompleteSqrtExtensionElement(FieldElement):
    def __init__(self, parent, u, v=Integer(1)):
        super().__init__(parent)
        base_ring = parent.base_ring()
        if isinstance(v, IncompleteSqrtExtensionElement):
            assert v.v.is_one()
            v = v.u
        if isinstance(u, IncompleteSqrtExtensionElement):
            v = u.v * v
            u = u.u
        u = base_ring(u)
        v = base_ring(v)
        if u.is_zero() or v.is_zero():
            u = v = base_ring.zero()
        elif v.is_square():
            u = u * v.sqrt()
            v = base_ring.one()
        self.u = u
        self.v = v

    def _repr_(self):
        if self.v.is_one() or self.v.is_zero():
            return f"{self.u}"
        elif self.u.is_one():
            return f"sqrt({self.v})"
        elif (-self.u).is_one():
            return f"-sqrt({self.v})"
        u = self.u if sum(w != 0 for w in self.u) == 1 else f"({self.u})"
        return f"{u} * sqrt({self.v})"

    def _latex_(self):
        u = latex(self.u)
        v = latex(self.v)
        if self.v.is_one() or self.v.is_zero():
            return u
        elif self.u.is_one():
            return LatexExpr(r"\sqrt{%s}" % v)
        elif (-self.u).is_one():
            return LatexExpr(r"-\sqrt{%s}" % v)
        if sum(w != 0 for w in self.u) > 1:
            u = r"\left(%s\right)" % u
        return LatexExpr(r"%s \cdot \sqrt{%s}" % (u, v))

    def _algebraic_(self, ring):
        return ring(self.u) * ring(self.v).sqrt()

    def _rational_(self, ring=Q):
        return ring(AA(self))

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
        return IncompleteSqrtExtensionElement(parent, self.u + u, self.v)

    def _mul_(self, other):
        parent = self.parent()
        u = self.u * other.u
        if self.v == other.v:
            u *= self.v
            v = parent.base_ring().one()
        else:
            v = self.v * other.v
        return IncompleteSqrtExtensionElement(parent, u, v)

    def _neg_(self):
        return IncompleteSqrtExtensionElement(self.parent(), -self.u, self.v)

    def __invert__(self):
        return IncompleteSqrtExtensionElement(self.parent(), Integer(1)/(self.u * self.v), self.v)

    def _richcmp_(self, other, op):
        return richcmp(self.u.sign() * self.u**2 * self.v, other.u.sign() * other.u**2 * other.v, op)

    def sqrt(self):
        assert self.v.is_one()
        assert self.u >= 0
        parent = self.parent()
        return IncompleteSqrtExtensionElement(parent, parent.base_ring().one(), self.u)

    
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
