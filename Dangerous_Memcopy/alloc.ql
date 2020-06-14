import cpp
import semmle.code.cpp.dataflow.TaintTracking
import Config
import Utils




from MyConfig cfg, DataFlow::PathNode alloc, FunctionCall memcpy,DataFlow::PathNode memcpy_dst, Expr size
where
    cfg.hasFlowPath(alloc, memcpy_dst)
    and
    memcpy.getArgument(0) = memcpy_dst.getNode().asExpr()
    and
    size = alloc.getNode().asExpr().(FunctionCall).getAnArgument().getAChild*()
    and
    if exists(VariableAccess va | size = va)
    then isNumber(size.(VariableAccess).getTarget())
    else size = size
select memcpy.getLocation()  as memcpy_location, 
alloc.getNode().getLocation()  as allocation_location, 
size

