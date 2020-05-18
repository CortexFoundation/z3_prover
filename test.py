import z3

import op


class Result:
    def __init__(self, status=z3.unknown):
        self.status = status
        self.model = {}


def z3_solver(expr):
    s = z3.Solver()
    s.add(expr)
    status = s.check()
    res = Result(status)
    if status == z3.sat:
        m = s.model()
        res.model = {d.name(): m[d] for d in m.decls()}
    return res

a = z3.BitVec('a', 32)
b = z3.BitVec('b', 32)
c = z3.BitVec('c', 32)

cstr = z3.And(
    op.InClosedInterval(a, 1, 15),
    op.InClosedInterval(b, 1, 15))
cstr = z3.And(cstr, c == a + b)
asrt = op.InClosedInterval(c, 1, 30)

a_ = z3.BitVec('c', 32)
b_ = z3.BitVec('a', 32)
c_ = z3.BitVec('b', 32)

cstr_ = z3.And(
    op.InClosedInterval(a_, 1, 15),
    op.InClosedInterval(b_, 1, 15))
cstr_ = z3.And(cstr_, c_ == a_ + b_)
asrt_ = op.InClosedInterval(c_, 1, 30)

prove = z3.Implies(cstr, asrt)
prove_ = z3.Implies(cstr_, asrt_)

p = z3.And(prove, prove_)
p = z3.simplify(p)


s = z3.Solver()
s.add(z3.Not(p))
print (s)
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
