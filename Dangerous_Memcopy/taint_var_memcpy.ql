import cpp
import semmle.code.cpp.dataflow.TaintTracking
import semmle.code.cpp.dataflow.internal.FlowVar
import semmle.code.cpp.controlflow.StackVariableReachability
import semmle.code.cpp.valuenumbering.GlobalValueNumbering
import Config



from VariableAccess va, MyConfig cfg, DataFlow::PathNode alloc, FunctionCall memcpy,DataFlow::PathNode memcpy_dst, Variable v, DataFlow::PathNode vars,  DataFlow::PathNode args
where 
    cfg.hasFlowPath(alloc, memcpy_dst)
    and
    memcpy.getArgument(0) = memcpy_dst.getNode().asExpr()
    and
    args.getNode().asExpr() = memcpy.getArgument(2)
    and
    TaintTracking::localExprTaint(vars.getNode().asExpr(), args.getNode().asExpr())
    and
    va = vars.getNode().asExpr()
    and
    exists
    (
        VariableAccess va_2 | alloc.getNode().asExpr().(FunctionCall).getAnArgument().getAChild*() = va_2
        and
        (
            (not va_2.getTarget() = va.getTarget())
            or
            globalValueNumber(va) = globalValueNumber(va_2)
        )
        
    )
    and v = va.getTarget()
select memcpy.getLocation() as memcpy_location, alloc.getNode().asExpr().getLocation() as allocation_location, v as value