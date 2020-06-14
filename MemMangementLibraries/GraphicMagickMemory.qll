import cpp
import semmle.code.cpp.models.interfaces.Allocation
import semmle.code.cpp.dataflow.DataFlow


class GraphicmagickAcquireMemory extends AllocationFunction {
  int sizeArg;
  

  GraphicmagickAcquireMemory() {
    exists(string name |
      
      hasGlobalName(name) and
      (
        // AcquireMagickMemory(const size_t size)
        name = "MagickMalloc" and sizeArg = 0
        or
        // MagickMallocAligned(const size_t alignment,const size_t size)
        name = "MagickMallocAligned" and sizeArg = 1
        or
        // MagickMallocCleared(const size_t size)
        name = "MagickMallocCleared" and sizeArg = 0
        // MagickAllocateMemory(type, size)
        or
        name = "MagickAllocateMemory" and sizeArg = 1
        or
        // MagickAllocateAlignedMemory(type, alignment, size)
        name = "MagickAllocateAlignedMemory" and sizeArg = 2
      )
    )
  }

  override int getSizeArg() { result = sizeArg }

}

class GraphicmagickAcquireMemoryBlocks extends AllocationFunction {
  int sizeArg;
  int multArg;

  GraphicmagickAcquireMemoryBlocks() {
    exists(string name |
      hasGlobalName(name) and
      (
        // MagickMallocAlignedArray(const size_t alignment,
//%                                     const size_t count,
//%                                     const size_t size);
        name = "MagickMallocAlignedArray" and sizeArg = 2 and multArg = 1
        or
        // MagickMallocArray(const size_t count, const size_t size);
        name = "MagickMallocArray" and sizeArg = 1 and multArg = 0
        or
        // MagickAllocateArray(type, const size_t count, const size_t size);
        name = "MagickAllocateArray" and sizeArg = 2 and multArg = 1
        // MagickAllocateAlignedArray(type, alignment, const size_t count, const size_t size);
        or
        name = "MagickAllocateAlignedArray" and sizeArg = 3 and multArg = 2
        
      )
    )
  }

  override int getSizeArg() { result = sizeArg }

  override int getSizeMult() { result = multArg }
}

class GraphicmagickAcquireBlob extends AllocationFunction {
  int sizeArg;
  int multArg;

  GraphicmagickAcquireBlob() {
    exists(string name |
      hasGlobalName(name) and
      (
        // AcquireQuantumMemory(const size_t count,const size_t quantum)
        name = "GetVirtualMemoryBlob" and sizeArg = 1 and multArg = 0 
      )
    )
  }

  override int getSizeArg() { result = sizeArg }

  override int getSizeMult() { result = multArg }
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

class GraphicmagickVirtualBlocCall extends AllocationExpr, FunctionCall {
  GraphicmagickAcquireBlob target;
  CallAllocationExpr  pred;

  GraphicmagickVirtualBlocCall() {
    target = getTarget() and
    // realloc(ptr, 0) only frees the pointer
    not (
      exists(target.getReallocPtrArg()) and
      getArgument(target.getSizeArg()).getValue().toInt() = 0
    ) and
    exists(
      DataFlow::Node source, DataFlow::Node sink, GraphicmagickAcquireMemoryBlocks calloc |
      calloc.getACallToThisFunction() = pred
      and
      source.asExpr() = pred
      and
      sink.asExpr() = getArgument(0)
      and
      DataFlow::localFlowStep(source, sink)
    )
  }

  
  Expr getAPredArgument() {result = pred.getAnArgument()}
  
  override Expr getSizeExpr() { result = pred.getSizeExpr() }

  override int getSizeMult() {
    // malloc with multiplier argument that is a constant
    result = pred.getSizeMult()
  }

  override int getSizeBytes() { result = pred.getSizeBytes() }

  override Expr getReallocPtr() { result = pred.getReallocPtr() }

  override predicate requiresDealloc() { pred.requiresDealloc() }
}