#include <stdarg.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <math.h>
#include <stdlib.h>

#include "common.h"
#include "compiler.h"
#include "debug.h"
#include "object.h"
#include "memory.h"
#include "value.h"
#include "vm.h"

VM vm;

static Value arrayPrepend(int argCount, Value* args);
static Value arrayAppend(int argCount, Value* args);
static Value arrayHead(int argCount, Value* args);
static Value arrayTail(int argCount, Value* args);
static Value arrayRest(int argCount, Value* args);
static Value dictRemove(int argCount, Value* args);

static void growStack() {
  int oldCapacity = vm.stackCapacity;
  vm.stackCapacity *= 2;
  vm.stack = GROW_ARRAY(Value, vm.stack, oldCapacity, vm.stackCapacity);
  vm.stackTop = vm.stack + oldCapacity;
}

static void growFrames() {
  int oldCapacity = vm.framesCapacity;
  vm.framesCapacity *= 2;
  vm.frames = GROW_ARRAY(CallFrame, vm.frames, oldCapacity, vm.framesCapacity);
}

static Value lengthNative(int argCount, Value* args) {
  if (argCount != 1) {
    runtimeError("SKILL ISSUE: length() takes exactly 1 argument.");
    return NIL_VAL;
  }

  if (IS_STRING(args[0])) {
    ObjString* string = AS_STRING(args[0]);
    return NUMBER_VAL((double)string->length);
  } else if (IS_ARRAY(args[0])) {
    ObjArray* array = AS_ARRAY(args[0]);
    return NUMBER_VAL((double)array->elements.count);
  } else {
    runtimeError("SKILL ISSUE: Argument to length() must be a string or an array.");
    return NIL_VAL;
  }
}

static Value clockNative(int argCount, Value* args) {
  return NUMBER_VAL((double)clock() / CLOCKS_PER_SEC);
}

static Value timeNative(int argCount, Value* args) {
  time_t currentTime = time(NULL);
  return NUMBER_VAL((double)currentTime);
}

static Value termNative(int argCount, Value* args) {
  if (argCount != 1 || !IS_STRING(args[0])) {
    runtimeError("SKILL ISSUE: term() takes exactly 1 string argument.");
    return NIL_VAL;
  }

  ObjString* command = AS_STRING(args[0]);
  int result = system(command->chars);

  return NUMBER_VAL((double)result);
}

static Value arrayPrepend(int argCount, Value* args) {
  if (argCount != 2 || !IS_ARRAY(args[0])) {
    runtimeError("SKILL ISSUE: prepend() takes exactly 2 arguments: array and value.");
    return NIL_VAL;
  }

  ObjArray* array = AS_ARRAY(args[0]);
  Value value = args[1];

  // shift elements to the right
  writeArray(array, NIL_VAL); // add a new slot at the end
  for (int i = array->elements.count - 1; i > 0; i--) {
    array->elements.values[i] = array->elements.values[i - 1];
  }
  array->elements.values[0] = value;

  return NIL_VAL;
}

static Value arrayAppend(int argCount, Value* args) {
  if (argCount != 2 || !IS_ARRAY(args[0])) {
    runtimeError("SKILL ISSUE: append() takes exactly 2 arguments: array and value.");
    return NIL_VAL;
  }

  ObjArray* array = AS_ARRAY(args[0]);
  Value value = args[1];

  writeArray(array, value);

  return NIL_VAL;
}

static Value arrayHead(int argCount, Value* args) {
  if (argCount != 1 || !IS_ARRAY(args[0])) {
    runtimeError("SKILL ISSUE: head() takes exactly 1 argument: array.");
    return NIL_VAL;
  }

  ObjArray* array = AS_ARRAY(args[0]);

  if (array->elements.count == 0) {
    runtimeError("SKILL ISSUE: head() called on an empty array.");
    return NIL_VAL;
  }

  Value value = array->elements.values[0];
  // shift elements to the left
  for (int i = 0; i < array->elements.count - 1; i++) {
    array->elements.values[i] = array->elements.values[i + 1];
  }
  array->elements.count--;

  return value;
}

static Value arrayTail(int argCount, Value* args) {
  if (argCount != 1 || !IS_ARRAY(args[0])) {
    runtimeError("SKILL ISSUE: tail() takes exactly 1 argument: array.");
    return NIL_VAL;
  }

  ObjArray* array = AS_ARRAY(args[0]);

  if (array->elements.count == 0) {
    runtimeError("SKILL ISSUE: tail() called on an empty array.");
    return NIL_VAL;
  }

  Value value = array->elements.values[array->elements.count - 1];
  array->elements.count--;

  return value;
}

static Value arrayRest(int argCount, Value* args) {
  if (argCount != 1 || !IS_ARRAY(args[0])) {
    runtimeError("SKILL ISSUE: rest() takes exactly 1 argument: array.");
    return NIL_VAL;
  }

  ObjArray* array = AS_ARRAY(args[0]);
  if (array->elements.count == 0) {
    runtimeError("SKILL ISSUE: rest() called on an empty array.");
    return NIL_VAL;
  }

  ObjArray* anewArray = newArray();
  for (int i = 1; i < array->elements.count; i++) {
    writeArray(anewArray, array->elements.values[i]);
  }

  return ARRAY_VAL(anewArray);
}

static Value dictRemove(int argCount, Value* args) {
  if (argCount != 2 || !IS_DICT(args[0]) || !IS_STRING(args[1])) {
    runtimeError("SKILL ISSUE: delete() takes exactly 2 arguments: dictionary and key.");
    return NIL_VAL;
  }

  ObjDict* dict = AS_DICT(args[0]);
  ObjString* key = AS_STRING(args[1]);
  tableDelete(&dict->items, key);

  return NIL_VAL;
}

static void resetStack() {
  vm.stackTop = vm.stack;
  vm.frameCount = 0;
  vm.openUpvalues = NULL;
}

static void runtimeError(const char* format, ...) {
  va_list args;
  va_start(args, format);
  vfprintf(stderr, format, args);
  va_end(args);
  fputs("\n", stderr);

  for (int i = vm.frameCount - 1; i >= 0; i--) {
    CallFrame* frame = &vm.frames[i];
    ObjFunction* function = frame->closure->function;
    size_t instruction = frame->ip - function->chunk.code - 1;
    int line = getLine(&function->chunk, instruction);
    fprintf(stderr, "[line %d] in ", line);
    if (function->name == NULL) {
      fprintf(stderr, "script\n");
    } else {
      fprintf(stderr, "%s()\n", function->name->chars);
    }
  }

  resetStack();
}

static void defineNative(const char* name, NativeFn function) {
  push(OBJ_VAL(copyString(name, (int)strlen(name))));
  push(OBJ_VAL(newNative(function)));
  tableSet(&vm.globals, AS_STRING(vm.stack[0]), vm.stack[1]);
  pop();
  pop();
}

void initVM() {
  vm.stackCapacity = INITIAL_STACK_MAX;
  vm.stack = ALLOCATE(Value, vm.stackCapacity);
  vm.stackTop = vm.stack;

  vm.framesCapacity = INITIAL_FRAMES_MAX;
  vm.frames = ALLOCATE(CallFrame, vm.framesCapacity);

  resetStack();
  vm.objects = NULL;

  initTable(&vm.globals);
  initTable(&vm.strings);

  vm.initString = NULL;
  vm.initString = copyString("init", 4);

  defineNative("clock", clockNative);
  defineNative("time", timeNative);
  defineNative("term", termNative);
  defineNative("prepend", arrayPrepend);
  defineNative("append", arrayAppend);
  defineNative("head", arrayHead);
  defineNative("tail", arrayTail);
  defineNative("rest", arrayRest);
  defineNative("remove", dictRemove);
  defineNative("length", lengthNative);
}

void freeVM() {
  freeTable(&vm.globals);
  freeTable(&vm.strings);
  vm.initString = NULL;
  FREE_ARRAY(Value, vm.stack, vm.stackCapacity);
  FREE_ARRAY(CallFrame, vm.frames, vm.framesCapacity);
  freeObjects();
}

void push(Value value) {
  if (vm.stackTop == vm.stack + vm.stackCapacity) {
    growStack();
  }
  *vm.stackTop = value;
  vm.stackTop++;
}

Value pop() {
  vm.stackTop--;
  return *vm.stackTop;
}

static Value peek(int distance) {
  return vm.stackTop[-1 - distance];
}

static bool call(ObjClosure* closure, int argCount) {
  if (argCount != closure->function->arity) {
    runtimeError("SKILL ISSUE: Expected %d arguments but got %d.", closure->function->arity, argCount);
    return false;
  }

  if (vm.frameCount == vm.framesCapacity) {
    growFrames();
  }

  CallFrame* frame = &vm.frames[vm.frameCount++];
  frame->closure = closure;
  frame->ip = closure->function->chunk.code;
  frame->slots = vm.stackTop - argCount - 1;
  return true;
}

static bool checkReturnType(ObjFunction* function, Value returnValue) {
  switch (function->returnType) {
    case TYPE_NONE:
      return true; // no return type specified, any value is allowed
    case TYPE_VOID:
      return IS_NIL(returnValue);
    case TYPE_INT:
    case TYPE_FLOAT:
      return IS_NUMBER(returnValue);
    case TYPE_STRING:
      return IS_STRING(returnValue);
    case TYPE_BOOL:
      return IS_BOOL(returnValue);
  }
  return false;
}

static bool callValue(Value callee, int argCount) {
  if (IS_OBJ(callee)) {
    switch (OBJ_TYPE(callee)) {
      case OBJ_BOUND_METHOD: {
        ObjBoundMethod* bound = AS_BOUND_METHOD(callee);
        vm.stackTop[-argCount - 1] = bound->receiver;
        return call(bound->method, argCount);
      }
      case OBJ_CLASS: {
        ObjClass* klass = AS_CLASS(callee);
        vm.stackTop[-argCount - 1] = OBJ_VAL(newInstance(klass));
        Value initializer;
        if (tableGet(&klass->methods, vm.initString,
                    &initializer)) {
          return call(AS_CLOSURE(initializer), argCount);
          } else if (argCount != 0) {
          runtimeError("SKILL ISSUE: Expected 0 arguments but got %d.",
                      argCount);
          return false;
        }
        return true;
      }
      case OBJ_CLOSURE:
        return call(AS_CLOSURE(callee), argCount);
      case OBJ_NATIVE: {
        NativeFn native = AS_NATIVE(callee);
        Value result = native(argCount, vm.stackTop - argCount);
        vm.stackTop -= argCount + 1;
        push(result);
        return true;
      }
      default:
        break; // non callable object type
    }
  }
  runtimeError("SKILL ISSUE: Can only call functions and classes.");
  return false;
}

static bool invokeFromClass(ObjClass* klass, ObjString* name, int argCount) {
  Value method;
  if (!tableGet(&klass->methods, name, &method)) {
    runtimeError("SKILL ISSUE: Undefined property '%s'.", name->chars);
    return false;
  }
  return call(AS_CLOSURE(method), argCount);
}

static bool invoke(ObjString* name, int argCount) {
  Value receiver = peek(argCount);

  if (!IS_INSTANCE(receiver)) {
    runtimeError("SKILL ISSUE: Only instances have methods.");
    return false;
  }

  ObjInstance* instance = AS_INSTANCE(receiver);

  Value value;
  if (tableGet(&instance->fields, name, &value)) {
    vm.stackTop[-argCount - 1] = value;
    return callValue(value, argCount);
  }

  return invokeFromClass(instance->klass, name, argCount);
}

static bool bindMethod(ObjClass* klass, ObjString* name) {
  Value method;
  if (!tableGet(&klass->methods, name, &method)) {
    runtimeError("SKILL ISSUE: Undefined property '%s'.", name->chars);
    return false;
  }

  ObjBoundMethod* bound = newBoundMethod(peek(0),
                                        AS_CLOSURE(method));
  pop();
  push(OBJ_VAL(bound));
  return true;
}

static ObjUpvalue* captureUpvalue(Value* local) {
  ObjUpvalue* prevUpvalue = NULL;
  ObjUpvalue* upvalue = vm.openUpvalues;
  while (upvalue != NULL && upvalue->location > local) {
    prevUpvalue = upvalue;
    upvalue = upvalue->next;
  }

  if (upvalue != NULL && upvalue->location == local) {
    return upvalue;
  }

  ObjUpvalue* createdUpvalue = newUpvalue(local);
  createdUpvalue->next = upvalue;

  if (prevUpvalue == NULL) {
    vm.openUpvalues = createdUpvalue;
  } else {
    prevUpvalue->next = createdUpvalue;
  }

  return createdUpvalue;
}

static void closeUpvalues(Value* last) {
  while (vm.openUpvalues != NULL &&
        vm.openUpvalues->location >= last) {
    ObjUpvalue* upvalue = vm.openUpvalues;
    upvalue->closed = *upvalue->location;
    upvalue->location = &upvalue->closed;
    vm.openUpvalues = upvalue->next;
  }
}

static void defineMethod(ObjString* name) {
  Value method = peek(0);
  ObjClass* klass = AS_CLASS(peek(1));
  tableSet(&klass->methods, name, method);
  pop();
}

static bool isFalsey(Value value) {
  return IS_NIL(value) || (IS_BOOL(value) && !AS_BOOL(value));
}

static void concatenate() {
  ObjString* b = AS_STRING(peek(0));
  ObjString* a = AS_STRING(peek(1));

  int length = a->length + b->length;
  char* chars = ALLOCATE(char, length + 1);
  memcpy(chars, a->chars, a->length);
  memcpy(chars + a->length, b->chars, b->length);
  chars[length] = '\0';

  ObjString* result = takeString(chars, length);
  pop();
  pop();
  push(OBJ_VAL(result));
}

static InterpretResult run() {
  CallFrame* frame = &vm.frames[vm.frameCount - 1];

  #define READ_BYTE() (*frame->ip++)

  #define READ_SHORT() \
      (frame->ip += 2, \
      (uint16_t)((frame->ip[-2] << 8) | frame->ip[-1]))

  #define READ_CONSTANT() \
    (frame->closure->function->chunk.constants.values[READ_BYTE()])

  #define READ_CONSTANT_LONG() \
    (frame->closure->function->chunk.constants.values[READ_SHORT()])

  #define READ_STRING() AS_STRING(READ_CONSTANT())
  #define BINARY_OP(valueType, op) \
    do { \
      if (!IS_NUMBER(peek(0)) || !IS_NUMBER(peek(1))) { \
        runtimeError("SKILL ISSUE: Operands must be numbers."); \
        return INTERPRET_RUNTIME_ERROR; \
      } \
      double b = AS_NUMBER(pop()); \
      double a = AS_NUMBER(pop()); \
      push(valueType(a op b)); \
    } while (false)

  for (;;) {
    #ifdef DEBUG_TRACE_EXECUTION
    printf("          ");
    for (Value* slot = vm.stack; slot < vm.stackTop; slot++) {
      printf("[ ");
      printValue(*slot);
      printf(" ]");
    }
    printf("\n");
    disassembleInstruction(&frame->closure->function->chunk,
        (int)(frame->ip - frame->closure->function->chunk.code));
    #endif
    uint8_t instruction;
    switch (instruction = READ_BYTE()) {
      case OP_CONSTANT: {
        Value constant = READ_CONSTANT();
        push(constant);
        break;
      }
      case OP_CONSTANT_LONG: {
        Value constant = READ_CONSTANT_LONG();
        push(constant);
        break;
      }
      case OP_NIL:      push(NIL_VAL); break;
      case OP_TRUE:     push(BOOL_VAL(true)); break;
      case OP_FALSE:    push(BOOL_VAL(false)); break;
      case OP_POP:      pop(); break;
      case OP_GET_LOCAL: {
        uint8_t slot = READ_BYTE();
        push(frame->slots[slot]);
        break;
      }
      case OP_SET_LOCAL: {
        uint8_t slot = READ_BYTE();
        frame->slots[slot] = peek(0);
        break;
      }
      case OP_GET_GLOBAL: {
        ObjString* name = READ_STRING();
        Value value;
        if (!tableGet(&vm.globals, name, &value)) {
          runtimeError("SKILL ISSUE: Undefined variable '%s'.", name->chars);
          return INTERPRET_RUNTIME_ERROR;
        }
        push(value);
        break;
      }
      case OP_DEFINE_GLOBAL: {
        ObjString* name = READ_STRING();
        tableSet(&vm.globals, name, peek(0));
        pop();
        break;
      }
      case OP_SET_GLOBAL: {
        ObjString* name = READ_STRING();
        if (tableSet(&vm.globals, name, peek(0))) {
          tableDelete(&vm.globals, name);
          runtimeError("SKILL ISSUE: Undefined variable '%s'.", name->chars);
          return INTERPRET_RUNTIME_ERROR;
        }
        break;
      }
      case OP_GET_UPVALUE: {
        uint8_t slot = READ_BYTE();
        push(*frame->closure->upvalues[slot]->location);
        break;
      }
      case OP_SET_UPVALUE: {
        uint8_t slot = READ_BYTE();
        *frame->closure->upvalues[slot]->location = peek(0);
        break;
      }
      case OP_GET_PROPERTY: {
        if (IS_INSTANCE(peek(0))) {
          ObjInstance* instance = AS_INSTANCE(peek(0));
          ObjString* name = READ_STRING();

          Value value;
          if (tableGet(&instance->fields, name, &value)) {
            pop(); // Instance.
            push(value);
            break;
          }

          if (!bindMethod(instance->klass, name)) {
            return INTERPRET_RUNTIME_ERROR;
          }
        } else if (IS_DICT(peek(0))) {
          ObjDict* dict = AS_DICT(peek(0));
          ObjString* name = READ_STRING();
          Value value = readDict(dict, name);
          pop(); // Dict.
          push(value);
        } else {
          runtimeError("SKILL ISSUE: Only instances and dictionaries have properties.");
          return INTERPRET_RUNTIME_ERROR;
        }
        break;
      }
      case OP_SET_PROPERTY: {
        if (IS_INSTANCE(peek(1))) {
          ObjInstance* instance = AS_INSTANCE(peek(1));
          tableSet(&instance->fields, READ_STRING(), peek(0));
          Value value = pop();
          pop();
          push(value);
        } else if (IS_DICT(peek(1))) {
          ObjDict* dict = AS_DICT(peek(1));
          writeDict(dict, READ_STRING(), peek(0));
          Value value = pop();
          pop();
          push(value);
        } else {
          runtimeError("SKILL ISSUE: Only instances and dictionaries have fields.");
          return INTERPRET_RUNTIME_ERROR;
        }
        break;
      }
      case OP_GET_SUPER: {
        ObjString* name = READ_STRING();
        ObjClass* superclass = AS_CLASS(pop());

        if (!bindMethod(superclass, name)) {
          return INTERPRET_RUNTIME_ERROR;
        }
        break;
      }
      case OP_EQUAL: {
        Value b = pop();
        Value a = pop();
        push(BOOL_VAL(valuesEqual(a, b)));
        break;
      }
      case OP_GREATER:  BINARY_OP(BOOL_VAL, >); break;
      case OP_LESS:     BINARY_OP(BOOL_VAL, <); break;
      case OP_BITWISE_AND: {
        if (IS_NUMBER(peek(0)) && IS_NUMBER(peek(1))) {
          int b = (int)AS_NUMBER(pop());
          int a = (int)AS_NUMBER(pop());
          push(NUMBER_VAL(a & b));
        } else {
          runtimeError("SKILL ISSUE: operands must be numbers.");
          return INTERPRET_RUNTIME_ERROR;
        }
        break;
      }
      case OP_BITWISE_OR: {
        if (IS_NUMBER(peek(0)) && IS_NUMBER(peek(1))) {
          int b = (int)AS_NUMBER(pop());
          int a = (int)AS_NUMBER(pop());
          push(NUMBER_VAL(a | b));
        } else {
          runtimeError("SKILL ISSUE: Operands must be two numbers.");
          return INTERPRET_RUNTIME_ERROR;
        }
        break;
      }
      case OP_BITWISE_XOR: {
        if (IS_NUMBER(peek(0)) && IS_NUMBER(peek(1))) {
          int b = (int)AS_NUMBER(pop());
          int a = (int)AS_NUMBER(pop());
          push(NUMBER_VAL(a ^ b));
        } else {
          runtimeError("SKILL ISSUE: Operands must be two numbers.");
          return INTERPRET_RUNTIME_ERROR;
        }
        break;
      }
      case OP_BITWISE_LS: {
        if (IS_NUMBER(peek(0)) && IS_NUMBER(peek(1))) {
          int b = (int)AS_NUMBER(pop());
          int a = (int)AS_NUMBER(pop());
          push(NUMBER_VAL(a << b));
        } else {
          runtimeError("SKILL ISSUE: Operands must be two numbers.");
          return INTERPRET_RUNTIME_ERROR;
        }
        break;
      }
      case OP_BITWISE_RS: {
        if (IS_NUMBER(peek(0)) & IS_NUMBER(peek(1))) {
          int b = (int)AS_NUMBER(pop());
          int a = (int)AS_NUMBER(pop());
          push(NUMBER_VAL(a >> b));
        } else {
          runtimeError("SKILL ISSUE: Operands must be two numbers.");
          return INTERPRET_RUNTIME_ERROR;
        }
        break;
      }
      case OP_BITWISE_NOT: {
        if (IS_NUMBER(peek(0))) {
          double value = AS_NUMBER(pop());
          int intValue = (int)value;
          int result = ~intValue;
          push(NUMBER_VAL(result));
        } else {
          runtimeError("SKILL ISSUE: Operand must be a number.");
          return INTERPRET_RUNTIME_ERROR;
        }
        break;
      }
      case OP_ADD: {
        if (IS_STRING(peek(0)) && IS_STRING(peek(1))) {
          concatenate();
        } else if (IS_NUMBER(peek(0)) && IS_NUMBER(peek(1))) {
          double b = AS_NUMBER(pop());
          double a = AS_NUMBER(pop());
          push(NUMBER_VAL(a + b));
        } else {
          runtimeError("SKILL ISSUE: Operands must be two numbers or two strings.");
          return INTERPRET_RUNTIME_ERROR;
        }
        break;
      }
      case OP_MODULO: {
        if (!IS_NUMBER(peek(0)) || !IS_NUMBER(peek(1))) {
          runtimeError("SKILL ISSUE: Operands must be numbers.");
          return INTERPRET_RUNTIME_ERROR;
        }
        double b = AS_NUMBER(pop());
        double a = AS_NUMBER(pop());
        if (b == 0) {
          runtimeError("SKILL ISSUE: Division by zero.");
          return INTERPRET_RUNTIME_ERROR;
        }
        push(NUMBER_VAL(fmod(a, b)));
        break;
      }
      case OP_SUBTRACT: BINARY_OP(NUMBER_VAL, -); break;
      case OP_MULTIPLY: BINARY_OP(NUMBER_VAL, *); break;
      case OP_DIVIDE:   BINARY_OP(NUMBER_VAL, /); break;
      case OP_NOT:
        push(BOOL_VAL(isFalsey(pop())));
        break;
      case OP_NEGATE:
        if (!IS_NUMBER(peek(0))) {
          runtimeError("SKILL ISSUE: Operand must be a number.");
          return INTERPRET_RUNTIME_ERROR;
        }
        push(NUMBER_VAL(-AS_NUMBER(pop())));
        break;
      case OP_OUT: {
        printValue(pop());
        printf("\n");
        break;
      }
      case OP_JUMP: {
        uint16_t offset = READ_SHORT();
        frame->ip += offset;
        break;
      }
      case OP_JUMP_IF_FALSE: {
        uint16_t offset = READ_SHORT();
        if (isFalsey(peek(0))) frame->ip += offset;
        break;
      }
      case OP_LOOP: {
        uint16_t offset = READ_SHORT();
        frame->ip -= offset;
        break;
      }
      case OP_CALL: {
        int argCount = READ_BYTE();
        if (!callValue(peek(argCount), argCount)) {
          return INTERPRET_RUNTIME_ERROR;
        }
        frame = &vm.frames[vm.frameCount - 1];
        break;
      }
      case OP_INVOKE: {
        ObjString* method = READ_STRING();
        int argCount = READ_BYTE();
        if (!invoke(method, argCount)) {
          return INTERPRET_RUNTIME_ERROR;
        }
        frame = &vm.frames[vm.frameCount - 1];
        break;
      }
      case OP_SUPER_INVOKE: {
        ObjString* method = READ_STRING();
        int argCount = READ_BYTE();
        ObjClass* superclass = AS_CLASS(pop());
        if (!invokeFromClass(superclass, method, argCount)) {
          return INTERPRET_RUNTIME_ERROR;
        }
        frame = &vm.frames[vm.frameCount - 1];
        break;
      }
      case OP_CLOSURE: {
        ObjFunction* function = AS_FUNCTION(READ_CONSTANT());
        ObjClosure* closure = newClosure(function);
        push(OBJ_VAL(closure));
        for (int i = 0; i < closure->upvalueCount; i++) {
          uint8_t isLocal = READ_BYTE();
          uint8_t index = READ_BYTE();
          if (isLocal) {
            closure->upvalues[i] =
                captureUpvalue(frame->slots + index);
          } else {
            closure->upvalues[i] = frame->closure->upvalues[index];
          }
        }
        break;
      }
      case OP_CLOSE_UPVALUE:
        closeUpvalues(vm.stackTop - 1);
        pop();
        break;
      case OP_RETURN: {
        Value result = pop();
        closeUpvalues(frame->slots);
        vm.frameCount--;
        if (vm.frameCount == 0) {
          pop();
          return INTERPRET_OK;
        }

        // only check return type if one is specified
        if (frame->closure->function->returnType != TYPE_NONE &&
            !checkReturnType(frame->closure->function, result)) {
          runtimeError("SKILL ISSUE: Invalid return type.");
          return INTERPRET_RUNTIME_ERROR;
        }

        vm.stackTop = frame->slots;
        push(result);
        frame = &vm.frames[vm.frameCount - 1];
        break;
      }
      case OP_CLASS:
        push(OBJ_VAL(newClass(READ_STRING())));
        break;
      case OP_INHERIT: {
        Value superclass = peek(1);
        if (!IS_CLASS(superclass)) {
          runtimeError("SKILL ISSUE: Superclass must be a class.");
          return INTERPRET_RUNTIME_ERROR;
        }

        ObjClass* subclass = AS_CLASS(peek(0));
        tableAddAll(&AS_CLASS(superclass)->methods,
                    &subclass->methods);
        pop(); // subclass
        break;
      }
      case OP_METHOD:
        defineMethod(READ_STRING());
        break;
      case OP_ARRAY: {
        int elementCount = READ_BYTE();
        ObjArray* array = newArray();
        for (int i = 0; i < elementCount; i++) {
          writeArray(array, peek(elementCount - i - 1));
        }
        for (int i = 0; i < elementCount; i++) {
          pop();
        }
        push(ARRAY_VAL(array));
        break;
      }
      case OP_OBJECT_GET: {
        if (IS_ARRAY(peek(1))) {
          if (!IS_NUMBER(peek(0))) {
            runtimeError("SKILL ISSUE: Array access requires a number.");
            return INTERPRET_RUNTIME_ERROR;
          }
          int index = AS_NUMBER(pop());
          ObjArray* array = AS_ARRAY(pop());
          push(readArray(array, index));
        } else if (IS_DICT(peek(1))) {
          if (!IS_STRING(peek(0))) {
            runtimeError("SKILL ISSUE: Dictionary keys must be strings.");
            return INTERPRET_RUNTIME_ERROR;
          }
          ObjString* key = AS_STRING(pop());
          ObjDict* dict = AS_DICT(pop());
          push(readDict(dict, key));
        } else {
          runtimeError("SKILL ISSUE: Only arrays and dictionaries support get set operations.");
          return INTERPRET_RUNTIME_ERROR;
        }
        break;
      }
      case OP_OBJECT_SET: {
        if (IS_ARRAY(peek(2))) {
          if (!IS_NUMBER(peek(1))) {
            runtimeError("SKILL ISSUE: Array access requires a number.");
            return INTERPRET_RUNTIME_ERROR;
          }
          Value value = peek(0);
          int index = AS_NUMBER(peek(1));
          ObjArray* array = AS_ARRAY(peek(2));
          array->elements.values[index] = value;
          pop();
          pop();
          pop();
          push(NIL_VAL);
        } else if (IS_DICT(peek(2))) {
          if (!IS_STRING(peek(1))) {
            runtimeError("SKILL ISSUE: Dictionary keys must be strings.");
            return INTERPRET_RUNTIME_ERROR;
          }
          Value value = peek(0);
          ObjString* key = AS_STRING(peek(1));
          ObjDict* dict = AS_DICT(peek(2));
          writeDict(dict, key, value);
          pop();
          pop();
          pop();
          push(NIL_VAL);
        } else {
          runtimeError("SKILL ISSUE: Only arrays and dictionaries support set operations.");
          return INTERPRET_RUNTIME_ERROR;
        }
        break;
      }
      case OP_DICT: {
        ObjDict* dict = newDict();
        int elementCount = READ_BYTE();
        for (int i = 0; i < elementCount; i++) {
          Value value = pop();
          Value key = pop();
          if (!IS_STRING(key)) {
            runtimeError("SKILL ISSUE: Dictionary keys must be strings.");
            return INTERPRET_RUNTIME_ERROR;
          }
          writeDict(dict, AS_STRING(key), value);
        }
        push(DICT_VAL(dict));
        break;
      }
    }
  }

  #undef READ_BYTE
  #undef READ_SHORT
  #undef READ_CONSTANT
  #undef READ_STRING
  #undef BINARY_OP
}


InterpretResult interpret(const char* source) {
  ObjFunction* function = compile(source);
  if (function == NULL) return INTERPRET_COMPILE_ERROR;

  push(OBJ_VAL(function));
  ObjClosure* closure = newClosure(function);
  pop();
  push(OBJ_VAL(closure));
  call(closure, 0);

  return run();
}
