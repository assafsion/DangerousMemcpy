import cpp
import semmle.code.cpp.models.interfaces.Allocation
import semmle.code.cpp.dataflow.DataFlow


class LibTiffMemcpy extends FunctionCall{
    LibTiffMemcpy(){
        exists(string name |
            name = "_TIFFmemcpy"
            and
            this.getTarget().getName() = name)
    }
}


class LibTiffAllocFunction extends AllocationFunction {
  int sizeArg;
  

  LibTiffAllocFunction() {
    exists(string name |
      
      hasGlobalName(name) and
      (
        
        name = "_TIFFmalloc" and sizeArg = 0
        or
        
        name = "_TIFFrealloc" and sizeArg = 1
        
      )
    )
  }

  override int getSizeArg() { result = sizeArg }

}



/**
 * An allocation expression that is a function call, such as call to `malloc`.
 */
class CallAllocationExpr extends AllocationExpr, FunctionCall {
  AllocationFunction target;

  CallAllocationExpr() {
    target = getTarget() and
    // realloc(ptr, 0) only frees the pointer
    not (
      exists(target.getReallocPtrArg()) and
      getArgument(target.getSizeArg()).getValue().toInt() = 0
    )
  }


  
  override Expr getSizeExpr() { result = getArgument(target.getSizeArg()) }

  override int getSizeMult() {
    // malloc with multiplier argument that is a constant
    result = getArgument(target.getSizeMult()).getValue().toInt()
    or
    // malloc with no multiplier argument
    not exists(target.getSizeMult()) and
    result = 1
  }

  override int getSizeBytes() { result = getSizeExpr().getValue().toInt() * getSizeMult() }

  override Expr getReallocPtr() { result = getArgument(target.getReallocPtrArg()) }

  override predicate requiresDealloc() { target.requiresDealloc() }
}

