"""Exact checks for optimal cyclotomic detectors, full gluing, and period formulas."""
import hashlib
import json
from collections import Counter
from datetime import datetime, timezone
from functools import lru_cache
from pathlib import Path

import sympy as sp
import mpmath
import verify_period_formulas as old

from verification_context import paper_reference

ROOT = Path(__file__).resolve().parent
z,s=old.z,old.s
COUNTS={}

def check(condition, category):
    if not condition:
        raise AssertionError(category)
    COUNTS[category]=COUNTS.get(category,0)+1

@lru_cache(maxsize=None)
def canonical(expression,p):
    return old.cyclotomic_normal_form(expression,p).as_expr()

def equal(left,right,p):
    return canonical(sp.cancel(left-right),p)==0

def matrix_equal(left,right,p,category):
    check(left.shape==right.shape,category+"_shape")
    for i in range(left.rows):
        for j in range(left.cols):
            check(equal(left[i,j],right[i,j],p),category)

def rational_vp(value,p):
    value=sp.Rational(value)
    if value==0:
        return 10**8
    a,b=abs(int(value.p)),abs(int(value.q))
    result=0
    while a%p==0:
        a//=p
        result+=1
    while b%p==0:
        b//=p
        result-=1
    return result

@lru_cache(maxsize=None)
def valuation(expression,p):
    value=canonical(expression,p)
    if value==0:
        return 10**8
    pi=sp.Symbol("pi")
    shifted=sp.Poly(sp.expand(value.subs(s,1+pi)),pi)
    return min((p-1)*rational_vp(coefficient,p)+power[0]
               for power,coefficient in shifted.terms() if coefficient!=0)

def smith_valuations(matrix,p):
    a=[[canonical(matrix[i,j],p) for j in range(matrix.cols)]
       for i in range(matrix.rows)]
    result=[]
    for q in range(min(matrix.shape)):
        best=min(((valuation(a[i][j],p),i,j)
            for i in range(q,matrix.rows) for j in range(q,matrix.cols)))
        v,i0,j0=best
        if v>=10**8:
            break
        a[q],a[i0]=a[i0],a[q]
        for row in a:
            row[q],row[j0]=row[j0],row[q]
        pivot=a[q][q]
        for i in range(q+1,matrix.rows):
            if a[i][q]!=0:
                factor=canonical(a[i][q]/pivot,p)
                check(valuation(factor,p)>=0,"integral_smith_row_operation")
                for j in range(q+1,matrix.cols):
                    a[i][j]=canonical(a[i][j]-factor*a[q][j],p)
                a[i][q]=sp.S.Zero
        for j in range(q+1,matrix.cols):
            if a[q][j]!=0:
                factor=canonical(a[q][j]/pivot,p)
                check(valuation(factor,p)>=0,"integral_smith_column_operation")
                a[q][j]=sp.S.Zero
        result.append(v)
    return sorted(result)

def hermite(k):
    n=2*k+1
    C=sp.zeros(n)
    for col in range(n):
        power,remainder=divmod(col,k)
        C[remainder,col]=s**power
        C[k+remainder,col]=col*s**power
        C[2*k,col]=1
    return C

def artin_action(k,b,a):
    M=sp.zeros(k)
    for col in range(k):
        power,remainder=divmod(b+a*col,k)
        M[remainder,col]=s**power
    return M

def full_action(k,b,a,p):
    relation=(z**k-s)**2*(z-1)
    n=2*k+1
    M=sp.zeros(n)
    for col in range(n):
        expression=sp.rem(z**(b+a*col),relation,z)
        poly=sp.Poly(expression,z)
        for row in range(n):
            M[row,col]=canonical(poly.nth(row),p)
    return M

def integral_lattice_checks(p,j,action_check):
    k=p**j
    n=2*k+1
    C=hermite(k)
    check(sp.cancel(C.det()-(k*s)**k*(1-s)**2)==0,"normalized_hermite_determinant")
    exponents=smith_valuations(C,p)
    expected=([0]*k+[j*(p-1)]*(k-1)+[1,j*(p-1)+1]) if j else [0,0,2]
    check(exponents==sorted(expected),"full_cyclotomic_smith_invariants")
    check(sum(exponents)==k*j*(p-1)+2,"full_comparison_length")
    inverse=C.inv()
    expected_max=j*(p-1)+1 if j else 2
    min_inverse=min(valuation(x,p) for x in inverse)
    check(min_inverse==-expected_max,"exact_comparison_denominator")
    for e in (1,2):
        relation=(z**k-s)**2*(z-1)
        actual=sp.rem((z**(p**(j+e))-1)/p**e,relation,z)
        proposed=s**(-1)/(s-1)*(z**k-s)*(z**k-1)
        ap=sp.Poly(actual,z)
        bp=sp.Poly(proposed,z)
        for i in range(n):
            check(equal(ap.nth(i),bp.nth(i),p),"higher_detecting_polynomial")
        check(min(valuation(bp.nth(i),p) for i in range(n))==-1,"higher_witness_exact_pi_denominator")
    if action_check:
        b,a=1,1+p
        M=full_action(k,b,a,p)
        A=artin_action(k,b,a)
        block=sp.diag(sp.kronecker_product(sp.Matrix([[1,0],[b,a]]),A),sp.ones(1))
        matrix_equal(C*M,block*C,p,"higher_integral_hermite_action")
        for entry in M:
            check(valuation(entry,p)>=0,"higher_action_integral_entries")
        b2,a2=2,1+2*p
        A2=artin_action(k,b2,a2)
        matrix_equal(A*A2,artin_action(k,b+a*b2,a*a2),p,"finite_artin_representation_law")
    return {"p":p,"j":j,"rank":n,"smith_valuations":exponents}

def artin_period_checks(p,j):
    k=p**j
    xi,alpha=sp.symbols("xi alpha",nonzero=True)
    cyclo=sp.cyclotomic_poly(p*k,xi)
    A=sp.Matrix(k,k,lambda r,i:alpha**(-(1+p*i))*xi**(-(1+p*i)*r))
    for b,a in [(1,1),(0,1+p),(2,1+2*p)]:
        W=artin_action(k,b,a).subs(s,xi**k)
        gA=A.xreplace({alpha:xi**b*alpha,xi:xi**a})
        difference=W*gA-A
        for entry in difference:
            numerator=sp.fraction(sp.cancel(entry))[0]
            check(sp.rem(numerator,cyclo,xi)==0,"weighted_vandermonde_artin_period")
    return {"p":p,"j":j,"artin_rank":k}

def tensor_period_checks():
    a,b,t,u,psi,Omega=sp.symbols("a b t u psi Omega",nonzero=True)
    K=sp.Matrix([[1,0],[-u/t,1/t]])
    action=sp.Matrix([[1,0],[b,a]])
    gK=K.xreplace({u:u+b*t,t:a*t})
    check(sp.simplify(action*gK-K)==sp.zeros(2),"kummer_period_identity")
    E=sp.diag(Omega,1/(t*Omega))
    Eaction=sp.diag(psi,a/psi)
    gE=E.xreplace({Omega:Omega/psi,t:a*t})
    check(sp.simplify(Eaction*gE-E)==sp.zeros(2),"ordinary_elliptic_period_identity")
    check(sp.cancel(E.det()-1/t)==0,"ordinary_elliptic_period_determinant")
    combined=sp.kronecker_product(K,E)
    gcombined=sp.kronecker_product(gK,gE)
    combined_action=sp.kronecker_product(action,Eaction)
    check(sp.simplify(combined_action*gcombined-combined)==sp.zeros(4),"mixed_elliptic_kummer_period_identity")
    dual=combined.inv().T/t
    gdual=dual.xreplace({u:u+b*t,t:a*t,Omega:Omega/psi})
    check(sp.simplify(a*combined_action.inv().T*gdual-dual)==sp.zeros(4),"mixed_tensor_tate_dual")
    check(sp.simplify(combined.T*dual-sp.eye(4)/t)==sp.zeros(4),"mixed_tensor_identity_evaluation")
    for p in (5,13,17,29):
        coefficient=(-1)**((p-1)//4)*sp.binomial((p-1)//2,(p-1)//4)
        check(int(coefficient)%p!=0,"displayed_cm_curve_ordinary_hasse_coefficient")

def run():
    lattices=[]
    for p,j,action_check in [(3,0,True),(3,1,True),(3,2,False),(5,0,True),(5,1,True),(7,0,True)]:
        lattices.append(integral_lattice_checks(p,j,action_check))
    artin=[]
    for p,j in [(3,0),(3,1),(3,2),(5,1)]:
        artin.append(artin_period_checks(p,j))
    tensor_period_checks()
    return lattices,artin

def main():
    started=datetime.now(timezone.utc).isoformat()
    try:
        lattices,artin=run()
        status,error="passed",None
    except Exception as exc:
        lattices,artin=[],[]
        status,error="failed",repr(exc)
    result={
        "status":status,"started_utc":started,"finished_utc":datetime.now(timezone.utc).isoformat(),
        "method":"Exact rational/cyclotomic polynomial arithmetic; independent discrete-valuation Smith elimination.",
        "sympy_version":sp.__version__,"mpmath_version":mpmath.__version__,
        "check_count":sum(COUNTS.values()),"checks_by_category":COUNTS,
        "lattice_examples":lattices,"artin_examples":artin,
        "paper_reference": paper_reference(),
        "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope":"Finite algebraic consistency checks. The general optimality, period-ring, and convergence arguments are written proofs in the manuscript.",
        "error":error
    }
    (ROOT/"extended_check_results.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({"status":status,"checks":sum(COUNTS.values()),"categories":COUNTS,"error":error}))
    return 0 if status=="passed" else 1

if __name__=="__main__":
    raise SystemExit(main())

