from incomplete_sqrt_extension import IncompleteSqrtExtension
from sage.functions.other import sqrt
from sage.matrix.constructor import Matrix
from sage.matrix.special import identity_matrix
from sage.matrix.special import ones_matrix
from sage.matrix.special import zero_matrix
from sage.rings.integer import Integer


class VectorError(ValueError):
    def __init__(self, msg, mat, row, col, diff, vec=None, cos=None):
        super().__init__(msg)
        self.mat = mat
        self.row = row
        self.col = col
        self.diff = diff
        self.vec = vec
        self.cos = cos


class Eigenspace:
    def __init__(self, dimension, cosines, ring=None, extend=True):
        self.dimension = Integer(dimension)
        cosines = Matrix([cosines])[0]
        if ring is None:
            ring = cosines.base_ring()
        if extend:
            ring = IncompleteSqrtExtension(ring)
        self.cosines = cosines.change_ring(ring)

    def _vector(self, A, b):
        v = [0] * self.dimension
        j = 0
        for i, c in enumerate(b):
            d = c - sum(A[i, k] * v[k] for k in range(j))
            if j < self.dimension and A[i, j] != 0:
                v[j] = d / A[i, j]
                j += 1
            elif d != 0:
                raise VectorError("Cannot obtain the specified inner products!", A, i, j, d, v, b)
        return (v, j)

    def vector(self, A, r):
        A = Matrix(A)
        v, _ = self._vector(A, list(map(self.cosines.__getitem__, r)))
        return Matrix([v])[0].change_ring(self.cosines.base_ring())

    def vectors(self, R):
        R = Matrix(R)
        A = zero_matrix(self.cosines.base_ring(), R.nrows(), self.dimension)
        B = R.apply_map(self.cosines.__getitem__)
        for i in range(R.nrows()):
            A[i], j = self._vector(A, B[i][:i])
            d = 1 - sum(x**2 for x in A[i][:j])
            if d < 0:
                raise VectorError("The norm of the obtained vector is larger than one!", A, i, j, d)
            if d > 0:
                if j == self.dimension:
                    raise VectorError("The norm of the obtained vector is smaller than one!", A, i, j, d)
                A[i, j] = sqrt(d)
        return A


def relmatrix(*Gs, vcs=None):
    G1, *Gr = Gs
    n = len(G1)
    if vcs is None:
        vcs = G1.vertices()
    assert all(n == len(G) for G in Gr)
    return (len(Gs) + 1) * (ones_matrix(n, n) - identity_matrix(n)) - \
        sum(i * G.am(vertices=vcs) for i, G in enumerate(reversed(Gs), 1))
