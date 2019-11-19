import z3
from z3.z3 import _coerce_exprs

_ops_manager = {}
def register_op(op_name):
    def wrapper(op):
        op.op_name = op_name
        _ops_manager[op_name] = op
        return op
    return wrapper


def _Int(name):
    #  return z3.Int(name)
    return z3.BitVec(name, 64)
def _IntVal(val):
    #  return z3.IntVal(val)
    return z3.BitVecVal(val, 64)
def _BitRange(val):
    #  return (2 ** (val - 1)) - 1
    #  bv = z3.Int2BV(val, 64)
    #  return z3.BV2Int(bv, True)
    return (1 << (val - 1)) - 1
def _Add(a, b):
    return a + b

def _Add_cstr(x, y):
    assert x.ctx_ref() == y.ctx_ref()
    a, b = _coerce_exprs(x, y)
    over_flow = z3.BoolRef(z3.Z3_mk_bvadd_no_overflow(x.ctx_ref(),
                x.as_ast(), y.as_ast(), True))
    print (over_flow)
    return over_flow

def bvadd_no_overflow(x, y, signed=False):
    assert x.ctx_ref()==y.ctx_ref()
    a, b = z3._coerce_exprs(x, y)
    return BoolRef(Z3_mk_bvadd_no_overflow(a.ctx_ref(), a.as_ast(), b.as_ast(), signed))

# _Int = z3.Int
# _IntVal = z3.IntVal

_INT32_MAX = (1 << 31) - 1
class _Base(object):
    op_name = "NONE" # override

    def __init__(self, *args, **attr):
        for v in args:
            if not isinstance(v, _Base):
                raise TypeError(
                    'Operator:%s only accept input _Base' % self.op_name)

        self._attr = attr
        self._childs = args
        self.v, self.p = None, None
        self._forward(*args, **self._attr)
        if self.v is None:
            raise TypeError(
                'Operator:%s seems to forget to set v(value)'
                'in func:_forward' % self.op_name)
        if self.p is None:
            raise TypeError(
                'Operator:%s seems to forget to set p(precision)'
                'in func:_forward' % self.op_name)

    def _forward(self, *args, **kwargs):
        raise NotImplementedError("current operator's logic mathmatic")

    def _cstr(self):
        raise NotImplementedError("current operator's constraint condition")

    def cstr(self):
        cstr = [c.cstr() for c in self._childs]
        return z3.And(*cstr, self._cstr())

    def asrt(self):
        """ Assert the data overflow problem.
        """
        cstr = [c.asrt() for c in self._childs]
        asrt = z3.And(- _INT32_MAX <= self.v,
                self.v <= _INT32_MAX)
        return z3.And(*cstr, asrt)

    def __add__(self, b):
        return Add(self, b)

    def __mul__(self, b):
        return Mul(self, b)

    def __sub__(self, b):
        return Sub(self, b)

def InClosedInterval(data, start, end):
    return z3.And(start <= data, data <= end)


@register_op("var")
class Var(_Base):
    def _forward(self, name=None, prec=None):
        assert name is not None
        self.v = _Int(name)
        # self.v = z3.BitVec(name, 32)
        if prec is None:
            self.p = _Int("p_%s" % name)
        else:
            self.p = _IntVal(prec)

    def _cstr(self):
        r = _BitRange(self.p)
        return z3.And(
                InClosedInterval(self.p, 1, 32),
                InClosedInterval(self.v, -r, r),
        )

def var(name, prec=None):
    return Var(name=name, prec=prec)


@register_op("scalar_add")
class Add(_Base):
    def _forward(self, a, b, name="add", assign=False):
        # The interger addition is deterministic
        self._v = _Add(a.v, b.v)
        self._p = _Add(z3.If(a.p > b.p, a.p, b.p), _IntVal(1))
        if assign:
            self.v, self.p = _Int(name), _Int("p_"+name)
        else:
            self.v, self.p = self._v, self._p

    def _cstr(self):
        a, b = self._childs
        cstr = z3.And(a.p < 32, b.p < 32)
        if self._attr.get("assign", False):
            cstr = z3.And(cstr,
                     self.v == self._v,
                     self.p == self._p,
                    )
        return cstr

    def asrt(self):
        r = _BitRange(self.p)
        return z3.And(
                #  self.v == self._v,
                #  self.p == self._p,
                InClosedInterval(self.p, 1, 32),
                InClosedInterval(self.v, -r, r),
        )

@register_op("scalar_sub")
class Sub(_Base):
    def _forward(self, a, b):
        # The interger subtraction is deterministic
        self.v = a.v - b.v
        self.p = z3.If(a.p > b.p, a.p, b.p) + 1

    def _cstr(self):
        a, b = self._childs
        return z3.And(
                InClosedInterval(a.p, 1, 16),
                InClosedInterval(b.p, 1, 16),
            )


@register_op("scalar_mul")
class Mul(_Base):
    def _forward(self, a, b):
        # The interger multiply is deterministic
        self.v = a.v * b.v
        self.p = a.p + b.p

    def _cstr(self):
        # TODO(wlt): no need to consider larger than 0?
        # refer to source code.
        a, b = self._childs
        return z3.And(
                InClosedInterval(a.p, 1, 16),
                InClosedInterval(b.p, 1, 16),
            )


def prove(statement):
    s = z3.Solver()
    s.add(z3.Not(statement))
    status = s.check()
    if status == z3.unsat:
        print ("Success: The model is deterministic")
    elif status == z3.sat:
        print ("Error: The model is undeterministic")
        m = s.model()
        for d in m.decls():
            print ("%s = %s" % (d.name(), m[d]))
    elif status == z3.unknown:
        print ("Error: The model cannot be proved to deterministic")


def prove_model(model, show_prop=False):
    cstr = model.cstr()
    s = z3.Solver()
    s.add(cstr)
    if show_prop:
        print ("Assumption: \n", cstr, "\n")
    if s.check() == z3.unsat:
        print ("Model cannot be satisfied, "
               "so it's proved to be deterministic")
        return

    asrt = model.asrt()
    if show_prop:
        print ("Assertion: \n", asrt, "\n")
    statement = z3.Implies(cstr, asrt)
    prove(statement)


if __name__ == "__main__":
    a, b = var('a'), var('b')
    #  c = Add(a, b, assign=False)
    #  stmt = z3.Implies(c.cstr(), c.asrt())
    #  print (z3.simplify(stmt))
    #  prove(stmt)
    #  prove_model(c, True)

    c2 = Add(a, b, assign=True)
    stmt2 = z3.Implies(c2.cstr(), c2.asrt())
    print (z3.simplify(stmt2).sexpr())
    prove(stmt2)
    #  prove(stmt == stmt2)
