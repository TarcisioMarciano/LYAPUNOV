# LYAPUNOV - Determination of Lyapounov functions for systems of Quasi-Polynomial ODE's.
#  2.0
# January 2025 - tmrf1962@gmail.com - dimarti@unb.br

# Introduction
# Implementation of the approach by Iram M. Gléria, Annibal Figueiredo and Tarcísio M. Rocha Filho for the determination of Lyapunov functions for Quasi-Polynomial systems, as descrbed in the following articles:
# 
# A. Figueirdo, I. M. Gléria, T. M. Rocha-Filho. Boundedness of solutions and Lyapunov functions in quasi-polynomial systems. Physics Letters A 268
# (2000) 335. doi:10.1016/S0375-9601(00)00175-4.
# 
#  I. M. Gléria, A. Figueiredo, T. M. Rocha-Filho. A numerical method for the stability analysis of quasi-polynomial vector fields. Nonlinear Analysis 52 (2003) 329. doi:10.1016/S0362-546X(02)00117-7.
# 
# Interface
# LYAPUNOV
# LyapunovFunction - Obtains the Lyapunov functions for a set of ODEs and a given fixed point by solving, if possible, the admissibility conditions.
# 
# lyap_func - Gives the form of the lyapunov function for a set of ODEs and a given fixed point without solving the admissibility conditions.
# 
# AdmissibilityConditions - Determines the admissibility conditions for a given set of ODEs and a given fixd point.
# 
# SolveCond - Solves the admissibility conditions.
# Implementation - Initialization
# Initialization
restart:

lyapunov := module()

export LyapunovFunction,lyap_func,AdmissibilityConditions,SolveAdmissCond,
       SolveSingleIneq,SolveManyIneqs,init:

local SolveConds,quad_matrix,comp_alpha,dimred,setcont2,gfr_alg,solve_minmax,compute_MP,
      highest_eigenvector,compute_g,gfr_cond,gfr_cond0,conds_alt,IneqLinSolver,
      remove_trivial,TypeIneqs,GiveIneq,SolveSimpleIneq,SimplifyIneq,FinalSimplify2,
      clean_conds,SolveConds0,makenormal,adjust_ineq_res,RemoveContradictions,wti,
      RemoveTrivial,ComplexityOrder:

option package, load = init:


# Initialization procedure
init:=proc()
global LYAPUNOV,SADE:

with(sade):
with(linalg):
with(LinearAlgebra):
with(Optimization):

SADE[nored]:=false:
SADE[cmax]:=1:

LYAPUNOV[_eps]:=10.0^(-12):
LYAPUNOV[_eps2]:=10.0^(-8):
LYAPUNOV[_maxiter]:=1000:
LYAPUNOV[_incog_name]:=a:
LYAPUNOV[_incog_w]:=w:
LYAPUNOV[_timelim]:=20.0:
LYAPUNOV[_nummaxQP]:=6:
LYAPUNOV[_groebner]:=true:
LYAPUNOV[_maxsize]:=500:

end:
# Implementation - LYAPUNOV
# comp_alpha
# Synopsis
# result := comp_alpha( )
# Parameters
# result : a matrix
# Description
# Computes the matrix alpha used as input to the lagrange algorithm.
# Code
comp_alpha:=proc()
local i,j,mm,n,k,alp,a:
global LYAPUNOV,SADE:
a:=LYAPUNOV[_incog_name]:
n:=nops(SADE[qmlist]):
mm:=array(1..n):
k:=0:
for i from 1 to n do
    if SADE[qmlist][i]=1 then
       k:=i
    fi
od:
if k=0 then
   mm:=SADE[matm]
else
   mm:=linalg[delrows](linalg[delcols](SADE[matm],k..k),k..k):
   n:=n-1
fi:
alp:=Matrix(n,n):
for i from 1 to n do
for j from 1 to n do
    alp[i,j]:=(cat(LYAPUNOV[_incog_name],i)*mm[i,j]+cat(LYAPUNOV[_incog_name],j)*mm[j,i])/2
od
od:
alp
end:
# quad_matrix
# Synopsis
# result := quad_matrix()
# Parameters
# result : a matrix.
# Description
# Return the LV matrix corresponding to the quadratic part (excluding the linear part associated to the monomial 1) of the Lotka-Volterra matrix stored in the SADE global variable SADE[matm].
# Code
quad_matrix:=proc()
local i,j,mm,n,k,alp,res:
global LYAPUNOV,SADE:

n:=nops(SADE[qmlist]):

mm:=array(1..n,1..n):
k:=0:
for i from 1 to n do
    if SADE[qmlist][i]=1 then
       k:=i
    fi
od:
if k=0 then
   mm:=SADE[matm]:
else
   mm:=linalg[delrows](linalg[delcols](SADE[matm],k..k),k..k):
   n:=n-1
fi:

res:=Matrix(n,n):
for i from 1 to n do
for j from 1 to n do
    res[i,j]:=mm[i,j]
od
od:
res:
end:
# dimred
# Synopsis
# result := dimred(alpha)
# Parameters
# input: a matrix.
# result : a matrix.
# Description
# Eliminates the first line and colum of the square matrix alpha of dimension n and
# returns a matrix with dimension n-1.
# Code
dimred:=proc(alpha)
local i,j,redalpha,n:
n:=LinearAlgebra[RowDimension](alpha):
redalpha:=Matrix(n-1,n-1):
for i from 2 to n do
for j from 2 to n do
    redalpha[i-1,j-1]:=alpha[i,j]
od
od:
redalpha
end:
# setcont2
# 
# 
# 
# Code
setcont2:=proc(a,s)
local res,i:
res:={}:
for  i from 1 to nops(s) do
     if has(a,s[i]) then
        res:=res union {s[i]}
     fi
od:
res
end:
# gfr_alg
# Synopsis
# result := gfr_alg(eq,ws,n,l)
# Parameters
# eq: a list or set with the equalities and inequatilities to solve;
# ws: a list with the unknown names.
# n: an integer - the numer of dimensions of the problem
# l: the step in the iteratove process.
# result : a set with logical conditions on the parameters.
# Description
# Gleria, Figueiredo & Rocha Filho Algorithm for solving F<=0.
# Code
gfr_alg:=proc(eq,ws,n,l)
local a,b,c,eq2,var,res,r1,r2:
global LYAPUNOV,SADE:

eq2:=expand(eq):
var:=ws[l]:

a:=coeff(eq2,var,2):
b:=coeff(eq2,var,1):
c:=coeff(eq2,var,0):

if l=n then
   r1:={a<0}:
   r2:={a=0,b=0}:
   res:=[r1,r2]:
   RETURN(res)
fi:

if l<=LYAPUNOV[_nummaxQP] then

   r1:=gfr_alg(b^2-4*a*c,ws,n,l+1):
   r2:=gfr_alg(c,ws,n,l+1):

   r1:=map(z->z union {a<0},r1):
   r2:=map(z->z union {a=0,b=0},r2):

   res:=[op(r1),op(r2)]
else

   r2:=gfr_alg(c,ws,n,l+1):

   r2:=map(z->z union {a=0,b=0},r2):

   res:=[op(r2)]
fi:

res

end:
# lyap_func
# Synopsis
# result := lyap_func(r,q,a)
# Parameters
# result : a function of the original variables.
# r: a set of substitution rules for the parameter values.
# q: a list of expressions for the components of the fixed point.
# a: if numeric implemets the numeric algorithm for the solution of the admissibility condition. Otherwise a list of values for the solution of the admissibility condition [a1,...,an].
# Description
# Computes the Lyapunov function if it exists for the values of the original parameters
# given in r and for the fixed point whose components are given in q in the respective
# order of the original variables as defined in algsys. The fixed point can be a function
# of the free parameters.
# Code
lyap_func:=proc(r,q2)
local i,j,nn,n2,bb,cc,res,a,fp,eqs,vrs,s,s2,unks,prov,n3,prov2,prov3,q,qq,anorm:
global LYAPUNOV,SADE:

qq:=simplify(subs(r,q2)):
vrs:=SADE[_vars]:

if args[3]<>numeric and not(type(args[3],list)) then
   RETURN("Wrong third argument,")
fi:

q:=SADE[qmlist]:
for i from 1 to nops(vrs) do
    if qq[i]=0 then RETURN(false) fi:
    q:=subs(qq[i],q)
od:

if args[3]=numeric then

   cc:=quad_matrix():
   nn:=LinearAlgebra[RowDimension](cc):

   for i from 1 to nn do
   for j from 1 to nn do
       cc[i,j]:=subs(r,cc[i,j]):
   od
   od:

   a:=Vector([seq(0.5,ii=1..nn)]):

   res:=solve_minmax(cc,a):

   if res=false then
      RETURN(false)
   fi:

   anorm:=0:
   for i from 1 to nn do
       anorm:=anorm+res[i]^2
   od:
   anorm:=sqrt(anorm):

   if anorm<LYAPUNOV[_eps2] then
      RETURN(false)
   fi:

   a:=res
else
   a:=args[3]:
   nn:=nops(a)
fi:

# Computes the Lyapunov function.
prov:=0:
j:=1:
for i from 1 to nn do
    if SADE[qmlist][i]<>1 then
       prov:=prov+a[j]*q[i]*(SADE[qmlist][i]/q[i]-ln(SADE[qmlist][i]/q[i])-1):
       j:=j+1
    fi
od:
res:=eval(subs(r,prov)):
res
end:
# solve_minmax
# Synopsis
# resulr := solve_minmax(M,a,norma)
# Parameters
# result : a vetor with the solution of the minimax problem.
# M: the Lotka-Volterra matrix.
# a: a vector with the initial guess.
# eps: maixmum error for phi
# eps2: maximum error as the norm of the variation of variable a
# Description
# Implementation of the numerical algorithm for the solution of the admissibility condition
#  of a matrix M as given in the article
#  "A numerical method for the stability analysis of quasi-polynomial vector $elds"
#  Nonlinear Analysis 52 (2003) 329 – 342.
# Code
solve_minmax:=proc(M,a)
local i,j,x,eqs_extra,eqn,delim,nn,ii,gg,mp,vv,ss,phi,err,sol,xx,aa,norma,eps,eps2,iter,pr:
global LYAPUNOV:

eps:=LYAPUNOV[_eps]:
eps2:=LYAPUNOV[_eps2]:

nn:=op(1,a):
mp:=Matrix(nn,nn):
gg:=Vector(nn):

aa:=Vector(nn):
for i from 1 to nn do
    aa[i]:=a[i]
od:

norma:=0:
for i from 1 to nn do
for j from 1 to nn do
    norma:=norma+M[i,j]^2
od
od:
norma:=sqrt(norma):

delim:={seq(x[ii]<=1,ii=1..nn),seq(x[ii]>=0,ii=1..nn),sp<=evalf(2*sqrt(nn)*norma),sp>=0}:

eqs_extra:=delim:

# Main loop

iter:=0:
err:=10^10:
xx:=[seq(x[ii],ii=1..nn)]:

while err>eps2 and iter<LYAPUNOV[_maxiter] do

      iter:=iter+1:

      for i from 1 to nn do
      for j from 1 to nn do
          mp[i,j]:=aa[i]*M[i,j]+M[j,i]*aa[j]
      od
      od:

      vv:=highest_eigenvector(mp,nn):

      for i from 1 to nn do
          pr:=0:
          for j from 1 to nn do
              pr:=pr+vv[i]*M[i,j]*vv[j]
          od:
          gg[i]:=2*pr:
      od:

      phi:=0:
      for i from 1 to nn do
          phi:=phi+gg[i]*aa[i]
      od:

      if phi<=eps then
         RETURN(aa)
      fi:

      eqn:=sp:
      for i from 1 to nn do
          eqn:=eqn+x[i]*gg[i]-aa[i]*gg[i]
      od:

      eqs_extra:=eqs_extra union {eqn<=0}:

      ss:=Optimization[LPSolve](-sp,eqs_extra,assume = nonnegative):
      sol:=subs(ss[2],xx):

      err:=0:
      for i from 1 to nn do
          err:=err+(sol[i]-aa[i])^2:
          aa[i]:=(sol[i]+aa[i])/2.0:
      end:
      err:=sqrt(err)
od:
false
end:
# highest_eigenvector
# Synopsis
# resut:=highest_eigenvector(M,n)
# Parameters
# M: a matrix.
# n: the dimension nXn of the matrix
# Description
# Returns the eigenvector corresponding to the highest eigenvaue of M.
# Code
highest_eigenvector:=proc(mp,n)
local i,ev,evec,l,lr,biggest,vec,imax:

vec:=Vector(1..n):

ev:=LinearAlgebra[Eigenvectors](mp):

l:=ev[1]:
evec:=ev[2]:

biggest:=-10^100:
for i from 1 to n do
    lr:=subs(I=0,l[i]):
    if lr>biggest then
       biggest:=lr:
       imax:=i
    fi
od:

for i from 1 to n do
    vec[i]:=subs(I=0,evec[i,imax])
od:

vec
end:
# gfr_cond
# Synopsis
# result := gfr_cond(params)
# Parameters
# result :  a set of sets of conditions.
# params: a set of variables.
# Description
# Obtains the conditions on admissibility given the parameters.
# Code
gfr_cond:=proc(params)
local i,j,l,Ma,alpha,n,ws,ii,aa,as,ww,res,eq,conds,c1,c2,cn,pr,pr2,pr3:
global SADE,LYAPUNOV:

alpha:=quad_matrix():
n:=LinearAlgebra[RowDimension](eval(alpha)):

Ma:=Matrix(n,n):
aa:=LYAPUNOV[_incog_name]:
ww:=LYAPUNOV[_incog_w]:

ws:=[seq(ww[ii],ii=1..n)];
as:=[seq(cat(aa,ii),ii=1..n)];

eq:=0:
for i from 1 to n do
for j from 1 to n do
    Ma[i,j]:=as[i]*alpha[i,j]:
    eq:=eq+Ma[i,j]*ww[i]*ww[j]
od
od:

LYAPUNOV[Ma_Matrix]:=Ma:

conds:=gfr_cond0(params):

conds

end:
# gfr_cond0
# Synopsis
# result := gfr_cond0(params)
# Parameters
# result :  a set of sets of conditions.
# params: a set of variables.
# Description
# Obtains the conditions on admissibility according ro Gléria, Figueredo & Rocha Filho algorithm.
# Code
gfr_cond0:=proc(params)
local res,res0,i,j,pr,pr2,eq,n,t1,t2,ws,ii,aas,aasb,aasc,aasd,aase,aasf:
global SADE,LYAPUNOV:

n:=LinearAlgebra[RowDimension](LYAPUNOV[Ma_Matrix]):

ws:=[seq(cat(LYAPUNOV[_incog_w],ii),ii=1..n)]:
aas:={seq(cat(LYAPUNOV[_incog_name],ii)>0,ii=1..n)}:
aasb:={seq(-cat(LYAPUNOV[_incog_name],ii)<0,ii=1..n)}:
aasc:={seq(cat(LYAPUNOV[_incog_name],ii)<0,ii=1..n)}:
aasd:={seq(-cat(LYAPUNOV[_incog_name],ii)>0,ii=1..n)}:
################################################
aase:={seq(cat(LYAPUNOV[_incog_name],ii)=0,ii=1..n)}:
aasf:={seq(-cat(LYAPUNOV[_incog_name],ii)=0,ii=1..n)}:
################################################

eq:=0:
for i from 1 to n do
for j from 1 to n do
    eq:=eq+LYAPUNOV[Ma_Matrix][i,j]*ws[i]*ws[j]
od
od:

res0:=gfr_alg(eq,ws,n,1):

res:={}:
for i from 1 to nops(res0) do
    pr:=res0[i]:
    t1:=expand(map(z->if type(z,`=`) then z fi,pr)):
    t2:=map(z->if type(z,`<`) or type(z,`<=`) then z fi,pr):

    t1:=map(z->lhs(z)-rhs(z),t1):
    t1:=map(z->coeffs(z,ws),t1) minus {0}:
    t1:=map(z->z=0,t1):

    pr:=t1 union t2:
    pr2:=map(z->if setcont2(z,params)={} then z fi,pr):
    pr2:=pr2 minus aas minus aasb:
    pr:=map(z->if has(z,0<0) then z fi,pr2):

    if pr={} and pr2 intersect aasc={} and pr2 intersect aasd={} and
                 pr2 intersect aase={} and pr2 intersect aasf={} then
       res:=res union {t1 union t2}
    fi:
od:

res

end:
# conds_alt
# Synopsis
# result := gfr_alt(eq,wws)
# Parameters
# result :  a set with a single set of conditions.
# eq: the equation of admissibility condition.
# wws: the set with the unknowns in eq.
# Description
# Obtains the conditions on admissibility ni the alternative form using the Hessian and the trace of matrix Ma.
# Code
conds_alt:=proc(eq,wws)
local rs,ee,i,j,pr,r1,r2,wws2,wws3,ee2,es,HH0,HH:

ee:=eq:
wws2:={op(wws)}:

HH0:=Matrix(nops(wws2),nops(wws2)):
for i from 1 to nops(wws2) do
for j from 1 to nops(wws2) do
    HH0[i,j]:=diff(diff(eq,wws2[i]),wws2[j])
od
od:

es:={}:
for i from 1 to nops(wws2) do
    pr:=0:
    for j from 1 to nops(wws2) do
        pr:=pr+HH0[i,j]*wws2[j]
    od:
    pr:=pr:
    es:=es union {pr}:
od:
es:=simplify(solve(es,wws2)):

r1:=map(z->if lhs(z)<>rhs(z) then lhs(z) fi,es):
r2:=map(z->if lhs(z)=rhs(z) then lhs(z) fi,es):

wws3:=r1:
ee2:=simplify(subs(map(z->z=0,r2),eq)):

HH:=Matrix(nops(wws3),nops(wws3)):
for i from 1 to nops(wws3) do
for j from 1 to nops(wws3) do
    HH[i,j]:=diff(diff(ee2,wws3[i]),wws3[j])
od
od:

rs:={factor(LinearAlgebra[Determinant](HH))>0}:
rs:={rs union {factor(LinearAlgebra[Trace](HH))<0}}:

rs

end:
# LyapunovFunction
# Synopsis
# result := LyapunovFunction(eqs,variables,params,fp)
# Parameters
# eqs : a list with the flow of the dynamical system.
# variables : a list with the variable names.
# paramas : a set with the free parameters in the flow.
# fp : a list with the components of the fixed point.
# Description
# Returns the Lyapunov functions, by solving the admissibility condition, either numerically or algebraicaly according to the problem.
# Code
LyapunovFunction:=proc(eqs::list,vars::list,params::set,fixpoint::list)
local res,MM,MM2,hv,z,uu,nn,mm,qq,conds,i,j,sol,sol2,pr,pr2,
      inc,inc2,lfunc,lfunc2,a,fp,as,assm,es:
global LYAPUNOV,SADE:

mm:=nops(vars):

# Obtaining the QP system
sade[algsys](eqs,vars,params):
MM:=quad_matrix():

nn:=LinearAlgebra[RowDimension](MM):
uu:=[seq(seq(MM[ii,jj],ii=1..nn),jj=1..nn)]:

hv:=map(z->has(uu,z),params):
qq:=[seq(vars[ii]=fixpoint[ii],ii=1..mm)]:

if hv={false} or hv={} then
   res:=lyap_func({1=1},qq,numeric)
else
   a:=LYAPUNOV[_incog_name]:

   fp:=subs(qq,SADE[qmlist]):

   lfunc:=0:
   j:=1:
   for i from 1 to nops(SADE[qmlist]) do
       if SADE[qmlist][i]<>1 then
          pr:=fp[i]*(SADE[qmlist][i]/fp[i]-ln(SADE[qmlist][i]/fp[i])-1):
          lfunc:=lfunc+cat(LYAPUNOV[_incog_name],j)*pr:
          j:=j+1
       fi
   od:

   conds:=AdmissibilityConditions(eqs,vars,params):

   if conds=false then RETURN({}) fi:

   as:={seq(cat(LYAPUNOV[_incog_name],ii),ii=1..nn)}:

   if has({args},assume) then
      assm:=op(map(z->if has(z,assume) then rhs(z) fi,{args})):
      sol:=SolveAdmissCond(conds,params,assume=assm):
   else
      sol:=SolveAdmissCond(conds,params):
   fi:

   res:=1:
   for i from 1 to nops(sol) do
       pr:=lfunc:
       
       es:=simplify(map(z->if type(z,`=`) then z fi,sol[i])):
       if es<>{} then
          pr:=traperror(timelimit(LYAPUNOV[_timelim],expand(subs(es,pr))))
       fi:

       if pr<>lasterror and nops(pr)<=LYAPUNOV[_maxsize] and not(type(pr,numeric)) then
          pr:=factor(pr):

          if type(pr,`*`) then
             lfunc2:=1:
             for j from 1 to nops(pr) do
                 if not(has(as,op(j,pr))) then
                    lfunc2:=lfunc2*op(j,pr)
                 fi
             od:
          else
             lfunc2:=pr
          fi:

          pr2:=map(z->if setcont2(lhs(z),as)<>{} then z fi,es):
          sol2:=map(z->if not(has(as,lhs(z))) or not(type(z,`=`)) then z fi,sol[i]):
          pr:=map(z->if has(as,lhs(z)) and rhs(z)<>0 then rhs(z)>0 fi,es):
          sol2:=pr union sol2:

          res:=res,[lfunc2,sol2]
       fi
   od:
   res:=[res]:
   res:=res[2..nops(res)]
fi:

res:=map(z->if not(has(z,false)) then z fi,res):

res

end:
# AdmissibilityConditions
# Synopsis
# result := AdmissibilityCOnditions(eqs,variables,params)
# Parameters
# eqs : a list with the flow of the dynamical system.
# variables : a list with the variable names.
# params : a set with the free parameters in the flow.
# Description
# Returns the admissibility conditions on the Lotka-Volterra matrix associated to the system.
# Code
AdmissibilityConditions:=proc(eqs::list,vars::list,params::set)
local res0,res,ws,i,cnd0,cnd1,cnd2,pr,pr2,qm,n,aas,aas2,ii:

sade[algsys](eqs,vars,params):
qm:=quad_matrix():
n:=LinearAlgebra[RowDimension](qm):
aas:={seq(cat(LYAPUNOV[_incog_name],ii),ii=1..n)}:
aas2:=map(z->z>0,aas):

res0:=gfr_cond(params):

res:={}:
for i from 1 to nops(res0) do

    pr:=res0[i]:
    cnd0:=map(z->if type(z,`=`) then z fi,pr):
    cnd1:=map(z->if type(z,`<`) then z fi,pr):
    cnd2:=map(z->if type(z,`<=`) then z fi,pr):

    cnd1:=map(z->lhs(z)-rhs(z),cnd1):
    cnd2:=map(z->lhs(z)-rhs(z),cnd2):

    cnd1:=clean_conds(cnd1,aas,1):
    cnd2:=clean_conds(cnd2,aas,-1):

    if cnd1<>false and cnd2<>false then
       pr:=cnd0 union cnd1 union cnd2: # union aas2:

       if nargs>=4 and has({args},Solve) then
          pr2:=IneqLinSolver(pr,aas,params):
          res:=res union {pr2}:
       else
          res:=res union {pr}
       fi
    fi
od:

if res<>{} and type(res[1],set) then
   res:=map(z->remove_trivial(z,aas),res)
else
   res:=remove_trivial(res,aas)
fi:

res:=res minus {{}} minus {{false}}:

res
end:
# Implementation - Algebraic solution of the adminissibility conditions
# IneqLinSolver
# Synopsis
# result := IneqLinSolver(ineqs,as,params)
# Parameters
# result : a list of conditions.
# ineqs: a set of inqualities
# as: a set with the ai's variables.
# paramas : a set with the free parameters in the flow.
# Description
# Solves the linear inequalities in the set ineqs and returns the solutions added with the non-lienar inequalities.
# Code
IneqLinSolver:=proc(ineqs::set,as::set,params::set)
local i,pr,ineqs_lin,ineqs_nonlin,ineqs_lin2,res,res2,eqs2,sol,sol2,as2,ww:

ww:=LYAPUNOV[_incog_w]:

if has(ineqs,ww[1]) then RETURN(ineqs) fi:

ineqs_lin:=map(z->if degree(lhs(z)-rhs(z),as)=1 and type(lhs(z)-rhs(z),polynom(anything,[op(as)])) then z fi,ineqs):
ineqs_nonlin:=ineqs minus ineqs_lin:

as2:=map(z->z>0,as):
eqs2:=map(z->if type(z,`=`) and lhs(z)<>rhs(z) then z fi,ineqs):

if ineqs_lin<>{} then
   ineqs_lin2:=ineqs_lin union as2:

   res:=solve(ineqs_lin2,as):
   if {res}={} or has(res,And) or has(res,Or) then
      res:=ineqs_lin
   else
      res:=res minus as2
   fi
else
   res:=ineqs
fi:

res:=res union ineqs_nonlin:

res

end:
# remove_trivial
# Synopsis
# result := remove_trivial(conds,as)
# Parameters
# result : a set of sets of conditions.
# conds: a set of sets of conditions.
# as: the set with the unknowns a.i
# Description
# Removes from the solutions obtained trivial conditions.
# Code
remove_trivial:=proc(conds0,as)
local i,j,res,pr,pr2,pr3,rmv,s,asz,asm,asp,conds,c1,c2,c3:

asz:=map(z->z=0,as):
asm:=map(z->z<0,as):
asp:=map(z->z>0,as) union map(z->-z<0,as):

c1:=map(z->if type(z,`=`) then lhs(z)-rhs(z)=0 fi,conds0):
c2:=map(z->if type(z,`<`) then lhs(z)-rhs(z)<0 fi,conds0):
c3:=map(z->if type(z,`<=`) then lhs(z)-rhs(z)<=0 fi,conds0):

conds:=c1 union c2 union c3 minus asp:

if setcont2(conds,asz)<>{} or setcont2(conds,asm)<>{} then
   RETURN({false})
fi:

rmv:={}:
res:={}:

for i from 1 to nops(conds) do
    pr:=conds[i]:

    if evalb(pr)=true then rmv:=rmv union {pr} fi:

    if type(pr,`=`) and lhs(pr)=rhs(pr) then
       rmv:=rmv union {pr}
    fi:    
 
    s:=0:
    if type(pr,`<=`) then s:=1 fi:
    if type(pr,`<`) then s:=-1 fi:

    if type(pr,`=`) and lhs(pr)=rhs(pr) and s<>0 then
       RETURN(false)
    fi:

    if s<>0 and evalb(pr)=false then RETURN({false}) fi:

    pr2:=factor(lhs(pr)-rhs(pr)):

    if s<>0 then
       if type(pr2,`*`) then
          pr3:=1:
          for j from 1 to nops(pr2) do
              if not(has(as,op(1,op(j,pr2)))) then
                 if type(op(j,pr2),`^`) then
                    if type(op(2,op(j,pr2)),even) or type(op(2,op(j,pr2)),odd) then
                       if type(op(2,op(j,pr2)),odd) and as minus {op(1,op(j,pr2))}=as then
                          if op(2,op(j,pr2))>0 then
                             pr3:=pr3*op(1,op(j,pr2))
                          else
                             pr3:=pr3/op(1,op(j,pr2))
                          fi
                       fi
                    else
                       pr3:=pr3*op(j,pr2)
                    fi
                 else
                    if type(op(j,pr2),numeric) then
                       if op(j,pr2)<0 then
                          pr3:=-pr3
                       fi
                    else
                       pr3:=pr3*op(j,pr2)
                    fi
                 fi
              fi
          od
       else
          pr3:=1:
          if not(has(as,op(1,pr2))) then
             if type(pr2,`^`) then
                if type(op(2,pr2),even) or type(op(2,pr2),odd) then
                    if type(op(2,pr2),odd) and as minus {op(1,pr2)}=as then
                       if op(2,pr2)>0 then
                          pr3:=pr3*op(1,pr2)
                       else
                          pr3:=pr3/op(1,pr2)
                       fi
                    fi
                 else
                    pr3:=pr3*pr2
                 fi
             else
                pr3:=pr2
             fi
          fi
       fi:

       if s=1 then
          if type(pr3,numeric) then
             if not(evalb(pr3<=0)) then RETURN({false}) fi
          else
             res:=res union {pr3<=0}
          fi
       else
          if type(pr3,numeric) then
             if not(evalb(pr3<0)) then RETURN({false}) fi
          else
             res:=res union {pr3<0}
          fi
       fi
    else
       res:=res union {conds[i]}
    fi:
od:

res:=res minus rmv:

res

end:
# TypeIneqs
# Synopsis
# result := TypeIneqs(inqs)
# Parameters
# result : an integer
# inqs: a set of sets of conditions.
# Description
# Return 0 if the inequality of of the <= type and 1 if the < type.
# Code
TypeIneqs:=proc(inqs)
local r:
r:=map(z->if type(z,`<=`) then 0 else if type(z,`<`) then 1 fi fi,inqs):
end:
# GivenIneq
# Synopsis
# result := GivenIneq(a,t)
# Parameters
# result : an inequation
# a: an algebraic expression.
# t: an integer.
# Description
# Returns a<=0 if t=0 and a<0 if t=1.
# Code
GiveIneq:=proc(a,t)
if t=0 then RETURN(a<=0) fi:
if t=1 then RETURN(a<0) fi:
ERROR()
end:
# SolveSimpleIneq
# Synopsis
# result := SolveSimpleIneq(ineq,as,params)
# Parameters
# result : a set of a set of solutions.
# ineq: am inequation.
# as: the set of ai's unknowns.
# params: the free parameters in the original set of equations.
# Description
# Solves a sinple simple inequation.
# Code
SolveSimpleIneq:=proc(ineq,as::set,params::set)
local res,i,k,pr,pr2,sols,eq,eq2,tq,prm,n,vars,vv,xx,cc,r:

vars:=as union params:
cc:=1:

eq:=factor(simplify(lhs(ineq)-rhs(ineq))):
if type(eq,`+`) then RETURN({{ineq}}) fi:

tq:=TypeIneqs({ineq})[1]:

if type(eq,`*`) then

   eq2:=1:
   for i from 1 to nops(eq) do
       pr:=op(i,eq):
       if type(pr,numeric) then
          cc:=cc*sign(pr)
       else
          eq2:=eq2*pr
       fi
   od:

   n:=nops(eq2):

   pr:=combinat[permute]([seq(1,ii=1..n),seq(-1,ii=1..n)], n):
   pr2:=map(z->convert(z,`*`),pr):

   prm:={}:
   for i from 1 to nops(pr) do
       if pr2[i]=-cc then
          prm:=prm union {pr[i]} 
       fi
   od:

   res:={}:
   for i from 1 to nops(prm) do
       r:={}:
       pr:=prm[i]:

       for k from 1 to nops(pr) do
           pr2:=op(k,eq2):

           if type(pr2,`^`) then
              xx:=op(2,pr2):

              if not(type(xx,integer)) then
                 if pr[k]=1 then
                    if tq=0 then
                       r:=r union {op(1,pr2)>=0}
                    else
                       r:=r union {op(1,pr2)>0}
                    fi
                 else
                    r:=r union {false}
                 fi:
              fi:

              if type(xx,even) then
                 if pr[k]=-1 then
                    r:=r union {false}
                 fi
              fi:

              if type(xx,odd) then
                 if tq=0 then
                       r:=r union {pr[k]*op(1,pr2)<=0}
                    else
                       r:=r union {pr[k]*op(1,pr2)<0}
                    fi
              fi:

           else
              r:=r union {GiveIneq(pr2*pr[k],tq)}
           fi
       od:

       if not(has(r,false)) then
          res:=res union {r}
       fi
   od:

   RETURN(res):
fi:

{{ineq}}

end:
# SolveSingleIneq
# Synopsis
# result := SolveSingleIneq(ineq,as,params)
# Parameters
# result : a set of a set of solutions.
# ineq: am inequation.
# as: the set of ai's unknowns.
# params: the free parameters in the original set of equations.
# Description
# Solves a single inequation.
# Code
SolveSingleIneq:=proc(ineq,as::set,params::set)
local i,res,sols:

sols:=SolveSingleIneq3(ineq,as,params):

#if nops(sols)=1 then RETURN(sols) fi:

res:={}:
for i from 1 to nops(sols) do
    res:=res union SolveManyIneqs(sols[i],as,params)
od:

res:=map(z->op(adjust_ineq_res(z,as)),res):

res:=map(z->RemoveContradictions(z),res) minus {{}}:
res:=map(z->RemoveTrivial(z,as,params),res) minus {{}}:

res

end:
# SolveSingleIneq2
# Synopsis
# result := SolveSingleIneq(ineq,as,params)
# Parameters2
# result : a set of a set of solutions.
# ineq: am inequation.
# as: the set of ai's unknowns.
# params: the free parameters in the original set of equations.
# Description
# Auziliary routine for solving a single inequation.
# Code
SolveSingleIneq2:=proc(ineq,as::set,params::set)
local res,sols,ti,ineq2,prm,n,i,j,sol0,linsol,lineq,eps,ntr,vars,as0,asm,ld,m,pr:

vars:=as union params:

as0:=map(z->z=0,as):
asm:=map(z->z<0,as) union map(z->-z>0,as):

if type(ineq,`<`) then ti:=1 fi:
if type(ineq,`<=`) then ti:=-1 fi:
if ti<>1 and ti<>-1 then ERROR("Bad format for an inequation.") fi:

ineq2:=lhs(ineq)-rhs(ineq):
sols:={solve(ineq2,vars)}:
sols:=map(w->map(z->if lhs(z)<>rhs(z) then z fi,w),sols):

sol0:=map(z->op(z),sols):

n:=nops(sol0):
prm:=combinat[permute]([seq(1,ii=1..n),seq(-1,ii=1..n)],n):

res:={}:
for i from 1 to nops(prm) do
    linsol:={}:
    lineq:={}:
    for j from 1 to n do
        ntr:=(lhs(sol0[j])-rhs(sol0[j]))*prm[i][j]<0:
        linsol:=linsol union {ntr}:
        lineq:=lineq union {lhs(sol0[j])=rhs(sol0[j])-prm[i][j]*eps}
    od:
    pr:=subs(lineq,ineq2):
    pr:=subs(lineq,pr):
    lineq:=simplify(pr):

    m:=0:
    pr:=subs(eps=0,lineq):
    while pr=0 do
          m:=m+1:
          pr:=simplify(subs(eps=0,diff(lineq,eps$m))):
    od:
    lineq:=pr:

    if linsol minus as0 minus asm=linsol then
       if ti=1 then
          lineq:=expand(lineq)<0
       else
          lineq:=expand(lineq)<=0
       fi:
       linsol:=linsol union {lineq}:

       if not(has(map(z->evalb(z),linsol),false)) then
          linsol:=map(z->if evalb(z)<>true then z fi,linsol):
          res:=res union {linsol}
       fi:
    fi:
od:

res

end:
# SolveSingleIneq3
# Synopsis
# result := SolveSingleIneq3(ineq,as,params)
# Parameters2
# result : a set of a set of solutions.
# ineq: am inequation.
# as: the set of ai's unknowns.
# params: the free parameters in the original set of equations.
# Description
# Auziliary routine for solving a single inequation.
# Code
SolveSingleIneq3:=proc(ineq,as::set,params::set)
local ti,eq,m,prm,i,new_ineqs,res:
if type(ineq,`<`) then ti:=1 fi:
if type(ineq,`<=`) then ti:=-1 fi:
if ti<>1 and ti<>-1 then ERROR("Bad format for an inequation.") fi:

eq:=factor(lhs(ineq)-rhs(ineq)):
if not(type(eq,`*`)) then
   RETURN(SolveSingleIneq2(ineq,as,params))
fi:

m:=nops(eq):

prm:=combinat[permute]([seq(1,ii=1..m),seq(-1,ii=1..m)],m):
prm:=map(z->if convert(z,`*`)=-1 then z fi,prm):

res:={}:
for i from 1 to nops(prm) do
    if ti=1 then
       new_ineqs:={seq(prm[i][ii]*op(ii,eq)<0,ii=1..m)}
    else
       new_ineqs:={seq(prm[i][ii]*op(ii,eq)<=0,ii=1..m)}
    fi:

    #res:=res union {SolveManyIneqs(new_ineqs,as,params)}
    res:=res union {new_ineqs}
od:

res:

end:
# SolveManyIneqs
# Synopsis
# result := SolveManyIneqs(ineqs,as,params)
# Parameters
# result : the solutiof of a set of inequalities
# ineqs: a set of inequations.
# a: the set of ai's unknowns.
# params: the set of free parameters inf the original differential equations.
# Description
# Solve a set of inequalities.
# Code
SolveManyIneqs:=proc(ineqs,as::set,params::set)
local i,res,pr,sols:
global vals:

sols:=table():
for i from  1 to nops(ineqs) do
    pr:=SolveSingleIneq3(ineqs[i],as,params):
    sols[i]:=pr:
od:

res:=sols[1]:
for i from 2 to nops(ineqs) do
    res:=map(w->op(map(z->z union w,res)),sols[i])
od:

res

end:
# SimplifyIneq
# Synopsis
# result := SimplifyIneq(ineqs)
# Parameters
# result: a set of simplified expressions
# ineqs: a set of inequaçities and equalities.
# Description
# Simplifies the set of expressions by putting all the terms on the left-and side.
# Code
SimplifyIneq:=proc(ineqs)
local res,pr,pr2,i:

res:={}:

for i from 1 to nops(ineqs) do
    pr:=ineqs[i]:
    if type(pr,`=`) then
       res:=res union {pr}
    else
       pr2:=lhs(pr)-rhs(pr):
       if type(pr,`<`) then
          res:=res union {pr2<0}
       else
          if type(pr,`<=`) then
             res:=res union {pr2<=0}
          else
             ERROR("Unknown type of expression.")
          fi
       fi
    fi
od:

res

end:
# FinalSimplify2
# Synopsis
# result := FinalSimplify2(conds,as)
# Parameters
# result : a set of inequalities and equalities.
# conds: a set of inequalities and equalities.
# as: a set with the ai's unknowns.
# Description
# Performs some final simplifications.
# Code
FinalSimplify2:=proc(conds,as,params)
local res,unks,ineqs,eqs,nm,ineqs_d1,sol:

unks:=as union params:

ineqs:=map(z->if not(type(z,`=`)) then z fi,conds):
eqs:=conds minus ineqs:
nm:=map(z->if type(evalf(lhs(z)-rhs(z)),numeric) then z fi,ineqs):

ineqs:=ineqs minus nm:

nm:=map(z->evalb(z),evalf(nm)):

if has(nm,false) then RETURN({false}) fi:

ineqs_d1:=map(z->if type(lhs(z)-rhs(z), polynom(algebraic,unks)) then z fi,ineqs):
ineqs_d1:=map(z->if degree(lhs(z)-rhs(z),unks)=1 then z fi,ineqs_d1):

sol:=solve(ineqs_d1,unks):

if {sol}={} then
   RETURN({false}):
#   sol:={false}#ineqs_d1
fi:

res:=ineqs minus ineqs_d1 union eqs union sol:
res:=map(z->if lhs(z)<>rhs(z) then z fi, res):

res

end:
# makenormal
# Synopsis
# result := makenormal(cond)
# Parameters
# result: a set of simplified expressions
# cond: an inequality or equality.
# Description
# Simplifies an equation such that it is on a polynomial form.
# Code
makenormal:=proc(cond)
local res,s,t1,t2,nn,dd,cond2:

if type(cond,`=`) then RETURN({{cond}}) fi:

if type(cond,`<`) then s:=-1 else s:=1 fi:

t1:=lhs(cond):
t2:=rhs(cond):

cond2:=simplify(t1-t2):

nn:=numer(cond2):
dd:=denom(cond2):

if s=-1 then
   res:={{-dd<0,nn<0},{dd<0,-nn<0}}
else
   res:={{-dd<=0,nn<0},{dd<=0,-nn<0}}
fi:

res

end:
# adjust_ineq_res
# Synopsis
# result := adjust_ineq_res(conds,as)
# Parameters
# result : a set of inequalities and equalities.
# conds: a set of inequalities and equalities.
# as: a set with the ai's unknowns.
# Description
# Performs some simplifications.
# Code
adjust_ineq_res:=proc(conds,as)
local res,i,j,pr,pr2,sol,asp,asm:

asp:=map(z->-z>0,as):
asm:=map(z->z<0,as):

res:=makenormal(conds[1]):
for i from 2 to nops(conds) do
    pr:=makenormal(conds[i]):
    for j from 1 to nops(pr) do
#        res:=map(w->map(z->z union w,pr),res)
        res:=map(w->op(map(z->z union w,pr)),res)
    od:
od:

sol:={}:
for i from 1 to nops(res) do
    pr:=map(z->if type(lhs(z),numeric) and type(rhs(z),numeric) then z fi,res[i]):
    pr2:=map(z->evalb(z),pr):
    if not(has(pr2,false)) and (res[i] intersect asp={}) and (res[i] intersect asm={}) then
       sol:=sol union map(w->map(z->if lhs(z)<>rhs(z) then z fi,w),{res[i] minus pr})
    fi
od:

sol

end:
# SolveAdmissCond
# Synopsis
# result := SolveAdmissCond(conds,params)
# Parameters
# result: a set with solutions of the admissibility conditions
# conds: a set if sets with the admissibility conditions.
# params: the free parameters in the original system.
# Description
# Solves the admissibility conditions.
# Code
SolveAdmissCond:=proc(conds,params)
local n,qm,sol,as,assm:
global LYAPUNOV,SADE:

qm:=quad_matrix():
n:=LinearAlgebra[RowDimension](qm):

as:={seq(cat(LYAPUNOV[_incog_name],ii),ii=1..n)}:

if has({args},assume) then
   assm:=op(map(z->if has(z,assume) then rhs(z) fi,{args})):
   sol:=SolveConds(conds,as,params,assume=assm):
else
   sol:=SolveConds(conds,as,params):
fi:

sol:=sol minus {{false}}:
sol:=map(z->op(adjust_ineq_res(z,as)),sol):

sol:=map(z->RemoveContradictions(z),sol) minus {{}}:
sol:=map(z->RemoveTrivial(z,as,params),sol) minus {{}}:
sol:=ComplexityOrder(sol):

sol

end:
# RemoveTrivial
# Synopsis
# result := RemoveTrivial(conds,aas,params)
# Parameters
# result : a set of inequalities and equalities.
# conds: a set of inequalities and equalities.
# aas: a set with the ai's unknowns.
# params: a set with the free parameters in the system.
# Description
# Removes trivial expressions from the conditions, such as -a1<0, -a1^2<0, ...
# Code
RemoveTrivial:=proc(c,aas,params)
local i, res,as2,pr,pr2,pr3,sc,sc2:

as2:=map(z->z>0,{op(aas)}):

res:={}:

for i from 1 to nops(c) do
    pr:=c[i]:
    sc:=setcont2(pr,params):
    sc2:=traperror(setcont2(pr,aas)):
    if sc={} and sc2={} then
       pr2:=evalb(evalf(pr))
    fi:
    if pr2=false then
       RETURN({})
    fi:

    if nops(sc2)=1 and sc={} then
       pr2:=solve({pr} union as2,aas):
       if {pr2}={} or pr2={{}} then
          RETURN({})
       fi:
       pr3:=lhs(pr)-rhs(pr):
       res:=res union pr2
    else
       res:=res union {pr}
    fi
od:
res:=res minus as2:

res

end:
# clean_conds
# Synopsis
# result:=clean_conds(conds,a,l)
# Parameters
# result :  a set of conditions
# conds: a set of conditions
# a: the set of variabl ai's
# l: an integer: if l=-1 returns inequalities of type <=. Otherwise returns of type <.
# Description
# removes the ai's (positive) multiplicative terms.
# Code
clean_conds:=proc(conds,a,l)
global LYAPUNOV:
local i,j,n,pr,pr2,trm,rs0,res,_c,aa:
rs0:={}:
aa:={op(a)}:
n:=nops(aa):
for i from 1 to nops(conds) do
    pr:=factor(_c*conds[i]):
    if type(pr,`*`) then
       pr2:=1:
       for j from 1 to nops(pr) do
           trm:=op(j,pr):

           if aa minus {trm}=aa then
              pr2:=pr2*trm
           fi:
       od:
       rs0:=rs0 union {pr2}
    fi
od:
rs0:=subs(_c=1,rs0):

res:={}:
for i from 1 to nops(rs0) do
    pr:=rs0[i]:
    if type(pr,numeric) then
       if pr>0 then
          RETURN(false)
       fi
    else
       if l=-1 then
          res:=res union {pr<=0}
       else
          res:=res union {pr<0}
       fi
    fi
od:

res

end:
# wti
# Synopsis
# SolveAdmissCond(cond)
# Parameters
# result: an integer. False if it is not a codition.
# cond: a single condition
# Description
# Returns 1 if the condition is an inequality of the type `<`, -1 if of type `<=`, 0 if it is an equality, and false otherwise.
# Code
wti:=proc(a)
if type(a,`<`) then RETURN(1) fi:
if type(a,`<=`) then RETURN(-1) fi:
if type(a,`=`) then RETURN(0) fi:
false
end:
# RemoveContradictions
# Synopsis
# result:=RemoveContradictions(conds)
# Parameters
# result :  a set of conditions
# conds: a set of conditions
# Description
# Identifies if a set of conditions is self-contradictory
# Code
RemoveContradictions:=proc(ac)
local i,j,res,res2,e1,e2,c2,t1,t2,pr,pr2,_gh,n,c:

c:=simplify(ac):
pr:=map(z->if type(lhs(z),numeric) and type(rhs(z),numeric) then evalb(z) fi,c):
if has(pr,false) then
   RETURN({})
fi:

res:={}:
for i from 1 to nops(c) do
    e1:=c[i]:
    t1:=wti(e1):
    for j from i+1 to nops(c) do
        e2:=c[j]:
        t2:=wti(e2):
        if t1<>0 and t2<>0 then
           pr:=traperror(simplify(lhs(e1)/lhs(e2))):
           if pr=lasterror then RETURN({}) fi:
           if type(pr,numeric) then
              if pr<0 then RETURN({}) fi
           fi
        fi
    od:
    res:=res union {simplify(e1)}
od:

res2:={}:
for i from 1 to nops(res) do
    e1:=c[i]:
    t1:=wti(e1):
    if t1<>0 then
       e2:=factor(lhs(e1)-rhs(e1)):
       if type(e2,`+`) then
          res2:=res2 union {e1}
       else
          e2:=e2*_gh:
          pr:=1:
          for j from 1 to nops(e2) do
              pr2:=op(j,e2):
              if type(pr2,`^`) then
                 n:=op(2,pr2):
                 if type(n,numeric) and type(n,odd) then
                    pr:=pr*op(1,pr2)
                 fi
              else
                 pr:=pr*pr2
              fi
          od:
          if t1=1 then
             pr:=pr<0
          else
             pr<=0
          fi:
          res2:=res2 union {subs(_gh=1,pr)}
       fi
    else
       res2:=res2 union {e1}
    fi
od:

res2

end:
# ComplexityOrder
# Synopsis
# result:=ComplexityOrder(conds)
# Parameters
# result :  a set of conditions
# conds: a set of conditions
# Description
# Reorder the conditions according to their complexity.
# Code
ComplexityOrder:=proc(c)
local i,j,ii,res,pr,comp_index,c2,mv,mt:

c2:={op(c)}:

res:=1:
while c2<>{} do
      mv:=10^10:
      for i from 1 to nops(c2) do
          pr:=c2[i]:
          pr:=map(z->nops(expand(lhs(z)-rhs(z))),pr):
          comp_index:=sum(pr[ii],ii=1..nops(pr)):
          if comp_index<mv then
             mt:=c2[i]:
             mv:=comp_index
          fi
      od:
      c2:=c2 minus {mt}:
      res:=res,mt
od:
res:=[res]:
res:=res[2..nops(res)]:

res

end:
# SolveConds0
# Synopsis
# result := SolveConds0(conds,as,params)
# Parameters
# result : a set of epressions (inequalities and equalities)
# as: the set with the ai's unknowns.
# params: the set of free parameters in the originnal differential system.
# Description
# Auxiliary routine to SolveConds. Perform a first step of the solution.
# Code
SolveConds0:=proc(conds::set,as::set,params::set)
local res_final,res,res2,sols,i,j,k,l,l2,ineqs,eqs,pr,pr2,res_f,ass,
      sol_eqs,vars,eqs2,eqs3,cde,cdi,cn:

if nargs=4 and lhs(args[4])=assume then
   ass:=rhs(args[4])
else
   ass:={}
fi:
ass:=[op(ass union {seq(as[ii]>0,ii=1..nops(as))})]:

cde:={seq(as[ii]=0,ii=1..nops(as))}:
cdi:={seq(as[ii]<0,ii=1..nops(as))}:

res_final:={}:

for k from 1 to nops(conds) do
    res:={}:

    ineqs:=map(z->if type(z,`<`) or type(z,`<=`) then z fi, conds[k]):
    if {ineqs}={} then ineqs:={} fi:
    eqs:=map(z->if type(z,`=`) then z fi, conds[k]):

    if {eqs}<>{} and eqs<>{} then

       vars:=setcont2(eqs,as union params):

       eqs3:=map(z->lhs(z)-rhs(z),eqs):

       if LYAPUNOV[_groebner]=true then
          eqs2:=traperror(Groebner[Basis](eqs3,plex(op(vars)))):
          if eqs2=lasterror then
             eqs2:=eqs3
          else
             eqs2:={op(eqs2)}:
          fi
       else
          eqs2:=eqs3
       fi:

       eqs:=traperror(timelimit(LYAPUNOV[_timelim],{solve(eqs2,vars)})):
       if eqs=lasterror then
          eqs:={map(z->z=0,eqs2)}
       else
          eqs:=map(z->allvalues(z),{op(eqs)}):
          eqs:=map(w->map(z->if lhs(z)<>rhs(z) then z fi,w),eqs)
       fi
    fi:

    sols:={}:
    if ineqs<>{} then
       sols:=traperror(timelimit(LYAPUNOV[_timelim],SolveManyIneqs(ineqs,as,params))):
       if sols=lasterror then
          sols:={ineqs}
       fi
    fi:
    sols:=map(z->if not(has(z,piecewise)) then z fi,sols):

    if sols={} then
       res:=res union eqs:
    else
       if eqs={} then
          res:=sols:
       else
          sols:=map(z->remove_trivial(z,as) minus {false},sols) minus {{}}:
          res2:=table:
          cn:=0:
          for l from 1 to nops(eqs) do
          for l2 from 1 to nops(sols) do
              pr:=traperror(timelimit(LYAPUNOV[_timelim],simplify(subs(eqs[l],sols[l2])))):
              if pr<>lasterror then
                 pr:=eqs[l] union pr:
                 cn:=cn+1:
                 res2[cn]:=pr:
              fi
          od
          od:
          res:={seq(res2[ii],ii=1..cn)}:
       fi:
    fi:

    res_final:=res_final union res:
od:

res:={}:
for i from 1 to nops(res_final) do
    pr:=timelimit(LYAPUNOV[_timelim],remove_trivial(res_final[i],as)):
    if pr=lasterror then
       res:=res union {res_final[i]}
    else
       res:=res union {pr}
    fi:
od:

res:=map(z->if not(has(z,false)) then z fi,res) minus {{}}:
res:=map(z->if not(has(z,I)) then z fi,res) minus {{}}:

res

end:
# SolveConds
# Synopsis
# result := SolveConds(conds,as,params)
# Parameters
# result : the solution of the set conds.
# conds: the set with the admissibility conditions.
# a: the set with the ai's unknowns.
# paramas: the set of free parameters in the original differential system.
# Description
# Solves the admissibility conditions.
# Code
SolveConds:=proc(conds::set,as::set,params::set)
local i,res,pr,pr0,ass,ass2,ass3,sol0:
global LYAPUNOV:

if nargs=4 and lhs(args[4])=assume then
   ass:=rhs(args[4])
else
   ass:={}
fi:

sol0:=traperror(SolveConds0(conds,as,params,assume=ass)):

if sol0=lasterror then
   sol0:=conds
fi:

pr:=map(w->map(z->if not(type(z,`=`)) and type(lhs(z),numeric) and type(rhs(z),numeric) then evalb(z) else z fi,w),sol0):
sol0:=map(z->if not(has(z,false)) then z fi,pr):
sol0:=map(z->z minus {true},sol0):

ass:={op(ass union {seq(as[ii]>0,ii=1..nops(as))})}:
ass2:=SimplifyIneq(ass):
ass3:=map(z->-lhs(z)<0,ass2):

#res:=1:
#for i from 1 to nops(sol0) do
#    pr0:=sol0[i]:
#   pr0:=map(z->if not(type(z,`=`) and lhs(z)=rhs(z)) then z fi,pr0):
#    #pr:=traperror(timelimit(LYAPUNOV[_timelim],SolveConds0({pr0},as,params,assume=ass3))):
#    pr:=SolveConds0({pr0},as,params,assume=ass3):
#
#    if pr=lasterror or pr={} then
#       pr:={sol0[i]}
#    fi:
#
#    res:=res,op(pr)
#od:
#res:={res}:
#res:=res[2..nops(res)]:

#res:=simplify(res,assume=[op(ass)]):
res:=simplify(sol0,assume=[op(ass)]):
res:=map(z->SimplifyIneq(z) minus ass2,res):
res:=map(z->if z intersect ass3={} and not(has(z,I)) then z fi,res):
res:=map(z->RemoveContradictions(z),res) minus {{}}:

res

end:
# Save
end module:

repo := "/home/marciano/simbolico/lyapunov/lib":
startdir := currentdir(repo):
march('create', "./LYAPUNOV.lib", 500):


savelibname := repo:
savelib('lyapunov');
restart:
# History
# LYAPUNOV Module:
# Beta Version: November 2001.
# Ver 1.0 May 9, 2002. 
# Ver 2.0 November 2024.

