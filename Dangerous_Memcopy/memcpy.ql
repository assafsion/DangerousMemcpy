import cpp
import Utils

from FunctionCall memcpy, Expr size
where 
    isMemcpy(memcpy)
    and
    size = memcpy.getArgument(2).getAChild*()
    and
    if exists(VariableAccess va | size = va)
    then isNumber(size.(VariableAccess).getTarget())
    else size = size

select memcpy.getLocation() as location, size as value