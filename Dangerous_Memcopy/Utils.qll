import cpp
import MemMangementLibraries.FFmpegMemory

predicate isNumber(Variable v){
    v.getUnspecifiedType() instanceof IntegralType
}

predicate isMemcpy(FunctionCall fc){
    fc.getTarget().hasName("memcpy")
}
