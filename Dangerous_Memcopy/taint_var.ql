import cpp
import semmle.code.cpp.dataflow.TaintTracking
import semmle.code.cpp.dataflow.internal.FlowVar
import semmle.code.cpp.controlflow.StackVariableReachability
import semmle.code.cpp.valuenumbering.GlobalValueNumbering
import Config

class VariableAccess2 extends VariableAccess{
    VariableAccess2(){
        this = this
    }

    predicate isModifiedBetweenExpressions(Expr e1, Expr e2){
        exists(
            Assignment assign | assign.getLValue() = this
            )
            and
            e1.getASuccessor*() = this
            and
            this.getASuccessor*() = e2
    }
}

predicate getAssignemntAfter(Expr e1, Expr e){
    e1.getASuccessor*() = e
}

predicate getAssignmentBefore(Expr e2, Expr e){
    e.getASuccessor*() = e2
}

AssignExpr getAssignmentBetween(Expr e1, Expr e2){
    
    getAssignemntAfter(e1, result)
    and
    getAssignmentBefore(e2, result)
    and
    not getAssignmentBefore(e1, result)
    and
    not getAssignemntAfter(e2, result) 
}

VariableAccess getVariableAccessBetween(Expr e1, Expr e2){
    getAssignemntAfter(e1, result)
    and
    getAssignmentBefore(e2, result)
    and
    not getAssignmentBefore(e1, result)
    and
    not getAssignemntAfter(e2, result) 
}

predicate isVariableAccessBetween(Expr e1, Expr e2, VariableAccess var){

    if var = e1 or e1 = e2
    then none()
    else e1.getASuccessor() = var or isVariableAccessBetween(e1.getASuccessor(), e2, var)

}

predicate isValidTaintedVar(FunctionCall memcpy, VariableAccess va){
    exists
    (
        VariableAccess va_memcpy | va_memcpy = memcpy.getArgument(2)
        and
        (
            (not va_memcpy.getTarget() = va.getTarget())
            or
            (globalValueNumber(va_memcpy) = globalValueNumber(va))
        )
    )
}


from VariableAccess va, MyConfig cfg, DataFlow::PathNode alloc, FunctionCall memcpy,DataFlow::PathNode memcpy_dst, Variable v, TaintedVarConfig test, DataFlow::PathNode vars,  DataFlow::PathNode args
where 
    cfg.hasFlowPath(alloc, memcpy_dst)
    and
    memcpy.getArgument(0) = memcpy_dst.getNode().asExpr()
    and
    args.getNode().asExpr() = alloc.getNode().asExpr().(FunctionCall).getAnArgument()
    and
    vars.getNode().asExpr().(VariableAccess).getEnclosingFunction() = memcpy.getEnclosingFunction()
    and
    test.hasFlowPath(vars, args)
    and
    va = vars.getNode().asExpr()
    and
    exists
    (
        VariableAccess va_2 | memcpy.getArgument(2).getAChild*() = va_2
        and
        (
            (not va_2.getTarget() = va.getTarget())
            or
            globalValueNumber(va) = globalValueNumber(va_2)
        )
        
    )
    and v = va.getTarget()
select memcpy.getLocation() as memcpy_location, alloc.getNode().asExpr().getLocation() as allocation_location, v as value