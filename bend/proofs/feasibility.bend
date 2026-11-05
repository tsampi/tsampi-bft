import Base
import ../model/kernel.bend as K

def trans(+a: K.ScannedTarget, +b: K.ScannedTarget, +c: K.ScannedTarget, ab: {a == b : K.ScannedTarget}, bc: {b == c : K.ScannedTarget}) -> {a == c : K.ScannedTarget}:
  %bc : {a == _ : K.ScannedTarget}
  ab

# Three completed Q1 advances finalize the starting target.
def three_quorum_steps_finalize(+base: K.ScannedTarget, +first: K.ScannedTarget, +second: K.ScannedTarget, +third: K.ScannedTarget, step1: {K.q1(first) == base : K.ScannedTarget}, step2: {K.q1(second) == first : K.ScannedTarget}, step3: {K.q1(third) == second : K.ScannedTarget}) -> {K.q3(third) == base : K.ScannedTarget}:
  a = Equal.cong(K.ScannedTarget,K.ScannedTarget,x => K.q1(K.q1(x)),K.q1(third),second,step3)
  b = Equal.cong(K.ScannedTarget,K.ScannedTarget,x => K.q1(x),K.q1(second),first,step2)
  trans(K.q3(third),K.q1(K.q1(second)),base,a,trans(K.q1(K.q1(second)),K.q1(first),base,b,step1))

# A fourth completed Q1 advance moves finality to the first new child.
def four_quorum_steps_finalize_new(+first: K.ScannedTarget, +second: K.ScannedTarget, +third: K.ScannedTarget, +fourth: K.ScannedTarget, step2: {K.q1(second) == first : K.ScannedTarget}, step3: {K.q1(third) == second : K.ScannedTarget}, step4: {K.q1(fourth) == third : K.ScannedTarget}) -> {K.q3(fourth) == first : K.ScannedTarget}:
  a = Equal.cong(K.ScannedTarget,K.ScannedTarget,x => K.q1(K.q1(x)),K.q1(fourth),third,step4)
  b = Equal.cong(K.ScannedTarget,K.ScannedTarget,x => K.q1(x),K.q1(third),second,step3)
  trans(K.q3(fourth),K.q1(K.q1(third)),first,a,trans(K.q1(K.q1(third)),K.q1(second),first,b,step2))
