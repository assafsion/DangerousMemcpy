import cpp
import RiskyLoop.ffmpeg.FFmpegMemory
import semmle.code.cpp.dataflow.TaintTracking
import semmle.code.cpp.dataflow.DataFlow
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.security.Overflow


from FunctionCall memcpy, CallAllocationExpr mall
where 
    
    memcpy.getTarget().hasName("memcpy") 
    and
    TaintTracking::localExprTaint(mall, memcpy.getArgument(0))

select memcpy.getLocation() as memcpy_location, mall.getLocation() as allocation_location

