#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <sys/stat.h>

#include "common.h"
#include "compiler.h"
#include "memory.h"
#include "scanner.h"

#ifdef DEBUG_PRINT_CODE
#include "debug.h"
#endif

typedef struct {
  Token current;
  Token previous;
  bool hadError;
  bool panicMode;
} Parser;

typedef enum {
  PREC_NONE,
  PREC_ASSIGNMENT,  // =
  PREC_OR,          // or
  PREC_AND,         // and
  PREC_EQUALITY,    // ==, !=
  PREC_COMPARISON,  // <, >, <=, >=
  PREC_TERM,        // +, -
  PREC_FACTOR,      // *, /
  PREC_BITWISE,     // &, ^, |, <<, >>, ~
  PREC_UNARY,       // !, -
  PREC_CALL,        // ., ()
  PREC_PRIMARY
} Precedence;

typedef void (*ParseFn)(bool canAssign);

typedef struct {
  ParseFn prefix;
  ParseFn infix;
  Precedence precedence;
} ParseRule;

typedef struct {
  Token name;
  int depth;
  bool isCaptured;
} Local;

typedef struct {
  uint8_t index;
  bool isLocal;
} Upvalue;

typedef enum {
  TYPE_FUNCTION,
  TYPE_INITIALIZER,
  TYPE_METHOD,
  TYPE_SCRIPT
} FunctionType;

typedef struct Compiler {
  struct Compiler* enclosing;
  ObjFunction* function;
  FunctionType type;

  Local locals[UINT8_COUNT];
  int localCount;
  Upvalue upvalues[UINT8_COUNT];
  int scopeDepth;
} Compiler;

typedef struct ClassCompiler {
  struct ClassCompiler* enclosing;
  bool hasSuperclass;
} ClassCompiler;

Parser parser;
Compiler* current = NULL;
ClassCompiler* currentClass = NULL;

static Chunk* currentChunk() {
  return &current->function->chunk;
}

static void errorAt(Token* token, const char* message) {
  if (parser.panicMode) return;
  parser.panicMode = true;
  fprintf(stderr, "[line %d] Error", token->line);

  if (token->type == TOKEN_EOF) {
    fprintf(stderr, " at end");
  } else if (token->type == TOKEN_ERROR) {
    // nothing
  } else {
    fprintf(stderr, " at '%.*s'", token->length, token->start);
  }

  fprintf(stderr, ": %s\n", message);
  parser.hadError = true;
}

static void error(const char* message) {
  errorAt(&parser.previous, message);
}

static void errorAtCurrent(const char* message) {
  errorAt(&parser.current, message);
}

static void advance() {
  parser.previous = parser.current;

  for (;;) {
    parser.current = scanToken();
    if (parser.current.type != TOKEN_ERROR) break;

    errorAtCurrent(parser.current.start);
  }
}

static void consume(TokenType type, const char* message) {
  if (parser.current.type == type) {
    advance();
    return;
  }

  errorAtCurrent(message);
}

static bool check(TokenType type) {
  return parser.current.type == type;
}

static bool match(TokenType type) {
  if (!check(type)) return false;
  advance();
  return true;
}

static void emitByte(uint8_t byte) {
  writeChunk(currentChunk(), byte, parser.previous.line);
}

static void emitBytes(uint8_t byte1, uint8_t byte2) {
  emitByte(byte1);
  emitByte(byte2);
}

static void emitLoop(int loopStart) {
  emitByte(OP_LOOP);

  int offset = currentChunk()->count - loopStart + 2;
  if (offset > UINT16_MAX) error("Loop body too large.");

  emitByte((offset >> 8) & 0xff);
  emitByte(offset & 0xff);
}

static int emitJump(uint8_t instruction) {
  emitByte(instruction);
  emitByte(0xff);
  emitByte(0xff);
  return currentChunk()->count - 2;
}

static void emitReturn() {
  if (current->type == TYPE_INITIALIZER) {
    emitBytes(OP_GET_LOCAL, 0);
  } else {
    emitByte(OP_NIL);
  }

  emitByte(OP_RETURN);
}

static uint8_t makeConstant(Value value) {
  int constant = addConstant(currentChunk(), value);
  if (constant > UINT8_MAX) {
    error("Too many constants in one chunk.");
    return 0;
  }

  return (uint8_t)constant;
}

static void emitConstant(Value value) {
  writeConstant(currentChunk(), value, parser.previous.line);
}

static void patchJump(int offset) {
  // -2 to adjust for the bytecode for the jump offset itself
  int jump = currentChunk()->count - offset - 2;

  if (jump > UINT16_MAX) {
    error("Too much code to jump over.");
  }

  currentChunk()->code[offset] = (jump >> 8) & 0xff;
  currentChunk()->code[offset + 1] = jump & 0xff;
}

static void initCompiler(Compiler* compiler, FunctionType type) {
  compiler->enclosing = current;
  compiler->function = NULL;
  compiler->type = type;
  compiler->localCount = 0;
  compiler->scopeDepth = 0;
  compiler->function = newFunction();
  current = compiler;
  if (type != TYPE_SCRIPT) {
    current->function->name = copyString(parser.previous.start, parser.previous.length);
  }

  Local* local = &current->locals[current->localCount++];
  local->depth = 0;
  local->isCaptured = false;
  if (type != TYPE_FUNCTION) {
    local->name.start = "this";
    local->name.length = 4;
  } else {
    local->name.start = "";
    local->name.length = 0;
  }
}

static ObjFunction* endCompiler() {
  emitReturn();
  ObjFunction* function = current->function;

  #ifdef DEBUG_PRINT_CODE
  if (!parser.hadError) {
    disassembleChunk(currentChunk(), function->name != NULL
        ? function->name->chars : "<script>");
  }
  #endif

  current = current->enclosing;
  return function;
}

static void beginScope() {
  current->scopeDepth++;
}

static void endScope() {
  current->scopeDepth--;

  while (current->localCount > 0 &&
          current->locals[current->localCount - 1].depth >
            current->scopeDepth) {
    if (current->locals[current->localCount - 1].isCaptured) {
      emitByte(OP_CLOSE_UPVALUE);
    } else {
      emitByte(OP_POP);
    }
    current->localCount--;
  }
}

static void expression();
static void statement();
static void declaration();
static ParseRule* getRule(TokenType type);
static void parsePrecedence(Precedence precedence);

static uint8_t identifierConstant(Token* name) {
  return makeConstant(OBJ_VAL(copyString(name->start, name->length)));
}

static ObjString* fetchImportName(Token* name) {
  return copyString(name->start, name->length);
}

static bool identifiersEqual(Token* a, Token* b) {
  if (a->length != b->length) return false;
  return memcmp(a->start, b->start, a->length) == 0;
}

static int resolveLocal(Compiler* compiler, Token* name) {
  for (int i = compiler->localCount - 1; i >= 0; i--) {
    Local* local = &compiler->locals[i];
    if (identifiersEqual(name, &local->name)) {
      if (local->depth == -1) {
        error("Can't read local variable in its own initializer.");
      }
      return i;
    }
  }

  return -1;
}

static int addUpvalue(Compiler* compiler, uint8_t index, bool isLocal) {
  int upvalueCount = compiler->function->upvalueCount;

  for (int i = 0; i < upvalueCount; i++) {
    Upvalue* upvalue = &compiler->upvalues[i];
    if (upvalue->index == index && upvalue->isLocal == isLocal) {
      return i;
    }
  }

  if (upvalueCount == UINT8_COUNT) {
    error("Too many closure variables in function.");
    return 0;
  }

  compiler->upvalues[upvalueCount].isLocal = isLocal;
  compiler->upvalues[upvalueCount].index = index;
  return compiler->function->upvalueCount++;
}

static int resolveUpvalue(Compiler* compiler, Token* name) {
  if (compiler->enclosing == NULL) return -1;

  int local = resolveLocal(compiler->enclosing, name);
  if (local != -1) {
    compiler->enclosing->locals[local].isCaptured = true;
    return addUpvalue(compiler, (uint8_t)local, true);
  }

  int upvalue = resolveUpvalue(compiler->enclosing, name);
  if (upvalue != -1) {
    return addUpvalue(compiler, (uint8_t)upvalue, false);
  }

  return -1;
}

static void addLocal(Token name) {
  if (current->localCount == UINT8_COUNT) {
    error("Too many local variables in function.");
    return;
  }
  Local* local = &current->locals[current->localCount++];
  local->name = name;
  local->depth = -1;
  local->isCaptured = false;
}

static void declareVariable() {
  if (current->scopeDepth == 0) return;

  Token* name = &parser.previous;
  for (int i = current->localCount - 1; i >= 0; i--) {
    Local* local = &current->locals[i];
    if (local->depth != -1 && local->depth < current->scopeDepth) {
      break;
    }

    if (identifiersEqual(name, &local->name)) {
      error("Already a variable with this name in this scope.");
    }
  }
  addLocal(*name);
}

static uint8_t parseVariable(const char* errorMessage) {
  consume(TOKEN_IDENTIFIER, errorMessage);

  declareVariable();
  if (current->scopeDepth > 0) return 0;

  return identifierConstant(&parser.previous);
}

void loadFile(char* name) {
  if (strlen(name) + 4 >= 256) {
    fprintf(stderr, "File name is too long.\n");
    return;
  }

  char nameCopy[256];
  strcpy(nameCopy, name);
  strcat(nameCopy, ".omg");
  
  char filePath[256];
  snprintf(filePath, sizeof(filePath), "./stl/%s", nameCopy);

  struct stat buffer;
  if (stat(filePath, &buffer) != 0) {
    snprintf(filePath, sizeof(filePath), "%s.omg", name);
  }

  FILE *file = fopen(filePath, "r");  // Open as a text file
  if (!file) {
    fprintf(stderr, "Failed to open file: %s\n", filePath);
    return;
  }

  fseek(file, 0, SEEK_END);
  size_t fileSize = ftell(file);
  fseek(file, 0, SEEK_SET);

  char *source = (char *)malloc(fileSize + 1);
  if (!source) {
    fprintf(stderr, "Failed to allocate memory for file: %s\n", filePath);
    fclose(file);
    return;
  }

  size_t index = 0;
  int c;
  while ((c = fgetc(file)) != EOF) {
    if (c == '\n' || c == '\r') {
      source[index++] = ' ';
    } else {
      source[index++] = (char)c;
    }
  }
  source[index] = '\0';

  fclose(file);

  InterpretResult result = interpret(source);
  free(source);

  if (result == INTERPRET_COMPILE_ERROR) exit(65);
  if (result == INTERPRET_RUNTIME_ERROR) exit(70);
}

static uint8_t parseImport(const char* errorMessage) {
  consume(TOKEN_IDENTIFIER, errorMessage);
  char* name = fetchImportName(&parser.previous)->chars;
  loadFile(name);
  return 0;
  // return name;
}

static void markInitialized() {
  if (current->scopeDepth == 0) return;
  current->locals[current->localCount - 1].depth =
    current->scopeDepth;
}

static void defineVariable(uint8_t global) {
  if (current->scopeDepth > 0) {
    markInitialized();
    return;
  }

  emitBytes(OP_DEFINE_GLOBAL, global);
}

static uint8_t argumentList() {
  uint8_t argCount = 0;
  if (!check(TOKEN_RIGHT_PAREN)) {
    do {
      expression();
      if (argCount == 255) {
        error("Can't have more than 255 arguments.");
      }
      argCount++;
    } while (match(TOKEN_COMMA));
  }
  consume(TOKEN_RIGHT_PAREN, "Expect ')' after arguments.");
  return argCount;
}

static void and_(bool canAssign) {
  int endJump = emitJump(OP_JUMP_IF_FALSE);

  emitByte(OP_POP);
  parsePrecedence(PREC_AND);

  patchJump(endJump);
}

static void binary(bool canAssign) {
  TokenType operatorType = parser.previous.type;
  ParseRule* rule = getRule(operatorType);
  parsePrecedence((Precedence)(rule->precedence + 1));

  switch (operatorType) {
    case TOKEN_BANG_EQUAL:    emitBytes(OP_EQUAL, OP_NOT); break;
    case TOKEN_EQUAL_EQUAL:   emitByte(OP_EQUAL); break;
    case TOKEN_GREATER:       emitByte(OP_GREATER); break;
    case TOKEN_GREATER_EQUAL: emitBytes(OP_LESS, OP_NOT); break;
    case TOKEN_LESS:          emitByte(OP_LESS); break;
    case TOKEN_LESS_EQUAL:    emitBytes(OP_GREATER, OP_NOT); break;
    case TOKEN_PLUS:          emitByte(OP_ADD); break;
    case TOKEN_MODULO:        emitByte(OP_MODULO); break;
    case TOKEN_MINUS:         emitByte(OP_SUBTRACT); break;
    case TOKEN_STAR:          emitByte(OP_MULTIPLY); break;
    case TOKEN_SLASH:         emitByte(OP_DIVIDE); break;
    case TOKEN_BITWISE_AND:   emitByte(OP_BITWISE_AND); break;
    case TOKEN_BITWISE_OR:    emitByte(OP_BITWISE_OR); break;
    case TOKEN_BITWISE_XOR:   emitByte(OP_BITWISE_XOR); break;
    case TOKEN_BITWISE_LS:    emitByte(OP_BITWISE_LS); break;
    case TOKEN_BITWISE_RS:    emitByte(OP_BITWISE_RS); break;
    default: return; // unreachable
  }
}

static void call(bool canAssign) {
  uint8_t argCount = argumentList();
  emitBytes(OP_CALL, argCount);
}

static void dot(bool canAssign) {
  consume(TOKEN_IDENTIFIER, "Expect property name after '.'.");
  uint8_t name = identifierConstant(&parser.previous);

  if (canAssign && match(TOKEN_EQUAL)) {
    expression();
    emitBytes(OP_SET_PROPERTY, name);
  } else if (match(TOKEN_LEFT_PAREN)) {
    uint8_t argCount = argumentList();
    emitBytes(OP_INVOKE, name);
    emitByte(argCount);
  } else {
    emitBytes(OP_GET_PROPERTY, name);
  }
}

static void literal(bool canAssign) {
  switch (parser.previous.type) {
    case TOKEN_FALSE: emitByte(OP_FALSE); break;
    case TOKEN_NIL:   emitByte(OP_NIL); break;
    case TOKEN_TRUE:  emitByte(OP_TRUE); break;
    default: return; // unreachable
  }
}

static void grouping(bool canAssign) {
  expression();
  consume(TOKEN_RIGHT_PAREN, "Expect ')' after expression.");
}

static void number(bool canAssign) {
  double value = strtod(parser.previous.start, NULL);
  emitConstant(NUMBER_VAL(value));
}

static void or_(bool canAssign) {
  int elseJump = emitJump(OP_JUMP_IF_FALSE);
  int endJump = emitJump(OP_JUMP);

  patchJump(elseJump);
  emitByte(OP_POP);

  parsePrecedence(PREC_OR);
  patchJump(endJump);
}

static void arrayLiteral(bool canAssign) {
  int elementCount = 0;
  if (!check(TOKEN_RIGHT_BRACKET)) {
    do {
      expression();
      elementCount++;
    } while (match(TOKEN_COMMA));
  }
  consume(TOKEN_RIGHT_BRACKET, "Expect ']' after array elements.");
  emitBytes(OP_ARRAY, elementCount);
}

static void dictLiteral(bool canAssign) {
  int elementCount = 0;
  if (!check(TOKEN_RIGHT_BRACE)) {
    do {
      expression();
      consume(TOKEN_COLON, "Expect ':' after key.");
      expression();
      elementCount++;
    } while (match(TOKEN_COMMA));
  }
  consume(TOKEN_RIGHT_BRACE, "Expect '}' after dict elements.");
  emitBytes(OP_DICT, elementCount);
}

static void objectAccess(bool canAssign) {
  expression();
  consume(TOKEN_RIGHT_BRACKET, "Expect ']' after index.");
  if (canAssign && match(TOKEN_EQUAL)) {
    expression();
    emitByte(OP_OBJECT_SET);
  } else {
    emitByte(OP_OBJECT_GET);
  }
}

static void string(bool canAssign) {
  emitConstant(OBJ_VAL(copyString(parser.previous.start + 1, parser.previous.length - 2)));
}

static void namedVariable(Token name, bool canAssign) {
  uint8_t getOp, setOp;
  int arg = resolveLocal(current, &name);
  if (arg != -1) {
    getOp = OP_GET_LOCAL;
    setOp = OP_SET_LOCAL;
  } else if ((arg = resolveUpvalue(current, &name)) != -1) {
    getOp = OP_GET_UPVALUE;
    setOp = OP_SET_UPVALUE;
  } else {
    arg = identifierConstant(&name);
    getOp = OP_GET_GLOBAL;
    setOp = OP_SET_GLOBAL;
  }
  
  if (canAssign && match(TOKEN_EQUAL)) {
    expression();
    emitBytes(setOp, (uint8_t)arg);
  } else {
    emitBytes(getOp, (uint8_t)arg);
  }
}

static void variable(bool canAssign) {
  namedVariable(parser.previous, canAssign);
}

static Token syntheticToken(const char* text) {
  Token token;
  token.start = text;
  token.length = (int)strlen(text);
  return token;
}

static void super_(bool canAssign) {
  if (currentClass == NULL) {
    error("Can't use 'super' outside of a class.");
  } else if (!currentClass->hasSuperclass) {
    error("Can't use 'super' in a class with no superclass.");
  }

  consume(TOKEN_DOT, "Expect '.' after 'super'.");
  consume(TOKEN_IDENTIFIER, "Expect superclass method name.");
  uint8_t name = identifierConstant(&parser.previous);

  namedVariable(syntheticToken("this"), false);
  if (match(TOKEN_LEFT_PAREN)) {
    uint8_t argCount = argumentList();
    namedVariable(syntheticToken("super"), false);
    emitBytes(OP_SUPER_INVOKE, name);
    emitByte(argCount);
  } else {
    namedVariable(syntheticToken("super"), false);
    emitBytes(OP_GET_SUPER, name);
  }
}

static void this_(bool canAssign) {
  if (currentClass == NULL) {
    error("Can't use 'this' outside of a class.");
    return;
  }

  variable(false);
} 

static void unary(bool canAssign) {
  TokenType operatorType = parser.previous.type;

  // compile the operand
  parsePrecedence(PREC_UNARY);

  // emit the operator instruction
  switch (operatorType) {
    case TOKEN_BANG:  emitByte(OP_NOT); break;
    case TOKEN_MINUS: emitByte(OP_NEGATE); break;
    case TOKEN_BITWISE_NOT: emitByte(OP_BITWISE_NOT); break;
    default: return; // unreachable
  }
}

ParseRule rules[] = {
  [TOKEN_LEFT_PAREN]    = {grouping,      call,         PREC_CALL},
  [TOKEN_RIGHT_PAREN]   = {NULL,          NULL,         PREC_NONE},
  [TOKEN_LEFT_BRACE]    = {dictLiteral,   NULL,         PREC_NONE}, 
  [TOKEN_RIGHT_BRACE]   = {NULL,          NULL,         PREC_NONE},
  [TOKEN_LEFT_BRACKET]  = {arrayLiteral,  objectAccess, PREC_CALL}, 
  [TOKEN_RIGHT_BRACKET] = {NULL,          NULL,         PREC_NONE},
  [TOKEN_COMMA]         = {NULL,          NULL,         PREC_NONE},
  [TOKEN_DOT]           = {NULL,          dot,          PREC_CALL},
  [TOKEN_COLON]         = {NULL,          NULL,         PREC_NONE},
  [TOKEN_MINUS]         = {unary,         binary,       PREC_TERM},
  [TOKEN_PLUS]          = {NULL,          binary,       PREC_TERM},
  [TOKEN_MODULO]        = {NULL,          binary,       PREC_TERM},
  [TOKEN_SEMICOLON]     = {NULL,          NULL,         PREC_NONE},
  [TOKEN_SLASH]         = {NULL,          binary,       PREC_FACTOR},
  [TOKEN_STAR]          = {NULL,          binary,       PREC_FACTOR},
  [TOKEN_BANG]          = {unary,         NULL,         PREC_NONE},
  [TOKEN_BANG_EQUAL]    = {NULL,          binary,       PREC_EQUALITY},
  [TOKEN_EQUAL]         = {NULL,          NULL,         PREC_NONE},
  [TOKEN_EQUAL_EQUAL]   = {NULL,          binary,       PREC_EQUALITY},
  [TOKEN_GREATER]       = {NULL,          binary,       PREC_COMPARISON},
  [TOKEN_GREATER_EQUAL] = {NULL,          binary,       PREC_COMPARISON},
  [TOKEN_LESS]          = {NULL,          binary,       PREC_COMPARISON},
  [TOKEN_LESS_EQUAL]    = {NULL,          binary,       PREC_COMPARISON},
  [TOKEN_IDENTIFIER]    = {variable,      NULL,         PREC_NONE},
  [TOKEN_STRING]        = {string,        NULL,         PREC_NONE},
  [TOKEN_NUMBER]        = {number,        NULL,         PREC_NONE},
  [TOKEN_AND]           = {NULL,          and_,         PREC_AND},
  [TOKEN_CLASS]         = {NULL,          NULL,         PREC_NONE},
  [TOKEN_ELSE]          = {NULL,          NULL,         PREC_NONE},
  [TOKEN_FALSE]         = {literal,       NULL,         PREC_NONE},
  [TOKEN_FOR]           = {NULL,          NULL,         PREC_NONE},
  [TOKEN_FN]            = {NULL,          NULL,         PREC_NONE},
  [TOKEN_IF]            = {NULL,          NULL,         PREC_NONE},
  [TOKEN_NIL]           = {literal,       NULL,         PREC_NONE},
  [TOKEN_OR]            = {NULL,          or_,          PREC_OR},
  [TOKEN_OUT]           = {NULL,          NULL,         PREC_NONE},
  [TOKEN_RETURN]        = {NULL,          NULL,         PREC_NONE},
  [TOKEN_SUPER]         = {super_,        NULL,         PREC_NONE},
  [TOKEN_THIS]          = {this_,         NULL,         PREC_NONE},
  [TOKEN_TRUE]          = {literal,       NULL,         PREC_NONE},
  [TOKEN_VAR]           = {NULL,          NULL,         PREC_NONE},
  [TOKEN_IMPORT]        = {NULL,          NULL,         PREC_NONE},
  [TOKEN_WHILE]         = {NULL,          NULL,         PREC_NONE},
  [TOKEN_ERROR]         = {NULL,          NULL,         PREC_NONE},
  [TOKEN_BITWISE_AND]   = {NULL,          binary,       PREC_BITWISE},
  [TOKEN_BITWISE_OR]    = {NULL,          binary,       PREC_BITWISE},
  [TOKEN_BITWISE_XOR]   = {NULL,          binary,       PREC_BITWISE},
  [TOKEN_BITWISE_LS]    = {NULL,          binary,       PREC_BITWISE},
  [TOKEN_BITWISE_RS]    = {NULL,          binary,       PREC_BITWISE},
  [TOKEN_BITWISE_NOT]   = {unary,         NULL,         PREC_BITWISE},
  [TOKEN_EOF]           = {NULL,          NULL,         PREC_NONE},
};

static void parsePrecedence(Precedence precedence) {
  advance();
  ParseFn prefixRule = getRule(parser.previous.type)->prefix;
  if (prefixRule == NULL) {
    error("Expect expression.");
    return;
  }

  bool canAssign = precedence <= PREC_ASSIGNMENT;
  prefixRule(canAssign);

  while (precedence <= getRule(parser.current.type)->precedence) {
    advance();
    ParseFn infixRule = getRule(parser.previous.type)->infix;
    infixRule(canAssign);
  }

  if (canAssign && match(TOKEN_EQUAL)) {
    error("Invalid assignment target.");
  }
}

static ParseRule* getRule(TokenType type) {
  return &rules[type];
}

static void expression() {
  parsePrecedence(PREC_ASSIGNMENT);
}

static void block() {
  while (!check(TOKEN_RIGHT_BRACE) && !check(TOKEN_EOF)) {
    declaration();
  }

  consume(TOKEN_RIGHT_BRACE, "Expect '}' after block.");
}

static FunctionReturnType parseReturnType() {
  if (match(TOKEN_AT)) {
  if (match(TOKEN_IDENTIFIER)) {
    if (parser.previous.length == 4 && memcmp(parser.previous.start, "void", 4) == 0) return TYPE_VOID;
    if (parser.previous.length == 3 && memcmp(parser.previous.start, "int", 3) == 0) return TYPE_INT;
    if (parser.previous.length == 5 && memcmp(parser.previous.start, "float", 5) == 0) return TYPE_FLOAT;
    if (parser.previous.length == 3 && memcmp(parser.previous.start, "str", 3) == 0) return TYPE_STRING;
    if (parser.previous.length == 4 && memcmp(parser.previous.start, "bool", 4) == 0) return TYPE_BOOL;
  }
  error("Invalid return type.");
  }
  return TYPE_NONE;
}

static void function(FunctionType type) {
  Compiler compiler;
  initCompiler(&compiler, type);
  beginScope();

  consume(TOKEN_LEFT_PAREN, "Expect '(' after function name.");
  if (!check(TOKEN_RIGHT_PAREN)) {
    do {
      current->function->arity++;
      if (current->function->arity > 255) {
        errorAtCurrent("Can't have more than 255 parameters.");
      }
      uint8_t constant = parseVariable("Expect parameter name.");
      defineVariable(constant);
    } while (match(TOKEN_COMMA));
  }
  consume(TOKEN_RIGHT_PAREN, "Expect ')' after parameters.");

  FunctionReturnType returnType = parseReturnType();
  current->function->returnType = returnType;

  consume(TOKEN_LEFT_BRACE, "Expect '{' before function body.");
  block();

  // if the function doesn't explicitly return and has no specified return type,
  // emit an implicit return
  if (current->function->chunk.code[current->function->chunk.count - 1] != OP_RETURN) {
    if (returnType == TYPE_VOID || returnType == TYPE_NONE) {
      emitReturn();
    } else {
      error("Function must have an explicit return.");
    }
  }

  ObjFunction* function = endCompiler();
  emitBytes(OP_CLOSURE, makeConstant(OBJ_VAL(function)));

  for (int i = 0; i < function->upvalueCount; i++) {
    emitByte(compiler.upvalues[i].isLocal ? 1 : 0);
    emitByte(compiler.upvalues[i].index);
  }
}

static void method() {
  consume(TOKEN_IDENTIFIER, "Expect method name.");
  uint8_t constant = identifierConstant(&parser.previous);

  FunctionType type = TYPE_METHOD;
  if (parser.previous.length == 4 &&
      memcmp(parser.previous.start, "init", 4) == 0) {
    type = TYPE_INITIALIZER;
  }

  function(type);
  emitBytes(OP_METHOD, constant);
}

static void classDeclaration() {
  consume(TOKEN_IDENTIFIER, "Expect class name.");
  Token className = parser.previous;
  uint8_t nameConstant = identifierConstant(&parser.previous);
  declareVariable();

  emitBytes(OP_CLASS, nameConstant);
  defineVariable(nameConstant);

  ClassCompiler classCompiler;
  classCompiler.hasSuperclass = false;
  classCompiler.enclosing = currentClass;
  currentClass = &classCompiler;

  if (match(TOKEN_LESS)) {
    consume(TOKEN_IDENTIFIER, "Expect superclass name.");
    variable(false);

    if (identifiersEqual(&className, &parser.previous)) {
      error("A class can't inherit from itself.");
    }

    beginScope();
    addLocal(syntheticToken("super"));
    defineVariable(0);

    namedVariable(className, false);
    emitByte(OP_INHERIT);
    classCompiler.hasSuperclass = true;
  }

  namedVariable(className, false);
  consume(TOKEN_LEFT_BRACE, "Expect '{' before class body.");
  while (!check(TOKEN_RIGHT_BRACE) && !check(TOKEN_EOF)) {
    method();
  }
  consume(TOKEN_RIGHT_BRACE, "Expect '}' after class body.");
  emitByte(OP_POP);

  if (classCompiler.hasSuperclass) {
    endScope();
  }

  currentClass = currentClass->enclosing;
}

static void fnDeclaration() {
  uint8_t global = parseVariable("Expect function name.");
  markInitialized();
  function(TYPE_FUNCTION);
  defineVariable(global);
}

static void varDeclaration() {
  uint8_t global = parseVariable("Expect variable name.");

  if (match(TOKEN_EQUAL)) {
    expression();
  } else {
    emitByte(OP_NIL);
  }
  consume(TOKEN_SEMICOLON, "Expect ';' after variable declaration.");
  defineVariable(global);
}

static void importDeclaration() {
  parseImport("Expect a file to import.");
  // if (match(TOKEN_EQUAL)) {
  //   expression();
  // } else {
  //   emitByte(OP_NIL);
  // }
  // consume(TOKEN_SEMICOLON, "Expect ';' after import declaration.");
  // loadFile(global);
}

static void expressionStatement() {
  expression();
  consume(TOKEN_SEMICOLON, "Expect ';' after expression.");
  emitByte(OP_POP);
}

static void forStatement() {
  beginScope();
  consume(TOKEN_LEFT_PAREN, "Expect '(' after 'for'.");
  if (match(TOKEN_SEMICOLON)) {
    // no initializer
  } else if (match(TOKEN_VAR)) {
    varDeclaration();
  } else {
    expressionStatement();
  }

  int loopStart = currentChunk()->count;
  int exitJump = -1;
  if (!match(TOKEN_SEMICOLON)) {
    expression();
    consume(TOKEN_SEMICOLON, "Expect ';' after loop condition.");

    // jump out of the loop if the condition is false
    exitJump = emitJump(OP_JUMP_IF_FALSE);
    emitByte(OP_POP); // condition
  }
  
  if (!match(TOKEN_RIGHT_PAREN)) {
    int bodyJump = emitJump(OP_JUMP);
    int incrementStart = currentChunk()->count;
    expression();
    emitByte(OP_POP);
    consume(TOKEN_RIGHT_PAREN, "Expect ')' after for clauses.");

    emitLoop(loopStart);
    loopStart = incrementStart;
    patchJump(bodyJump);
  }

  statement();
  emitLoop(loopStart);

  if (exitJump != -1) {
    patchJump(exitJump);
    emitByte(OP_POP); // condition
  }

  endScope();
}

static void ifStatement() {
  consume(TOKEN_LEFT_PAREN, "Expect '(' after 'if'.");
  expression();
  consume(TOKEN_RIGHT_PAREN, "Expect ')' after condition.");

  int thenJump = emitJump(OP_JUMP_IF_FALSE);
  emitByte(OP_POP);
  statement();

  int elseJump = emitJump(OP_JUMP);

  patchJump(thenJump);
  emitByte(OP_POP);

  if (match(TOKEN_ELSE)) statement();
  patchJump(elseJump);
}

static void outStatement() {
  expression();
  consume(TOKEN_SEMICOLON, "Expect ';' after value.");
  emitByte(OP_OUT);
}

static void returnStatement() {
  if (current->type == TYPE_SCRIPT) {
    error("Can't return from top-level code.");
  }

  if (match(TOKEN_SEMICOLON)) {
    if (current->function->returnType != TYPE_VOID) {
      error("Function must return a value.");
    }
    emitReturn();
  } else {
    if (current->function->returnType == TYPE_VOID) {
      error("Void function cannot return a value.");
    }

    expression();
    consume(TOKEN_SEMICOLON, "Expect ';' after return value.");
    
    // instead of checking the actual value, we'll do a basic type check based on the last emitted opcode
    uint8_t lastOpcode = current->function->chunk.code[current->function->chunk.count - 1];
    
    switch (current->function->returnType) {
      case TYPE_INT:
      case TYPE_FLOAT:
        if (lastOpcode != OP_CONSTANT && lastOpcode != OP_ADD && 
            lastOpcode != OP_SUBTRACT && lastOpcode != OP_MULTIPLY && 
            lastOpcode != OP_DIVIDE && lastOpcode != OP_NEGATE) {
          error("Function must return a number.");
        }
        break;
      case TYPE_STRING:
        if (lastOpcode != OP_CONSTANT) {  // assuming strings are always constants
          error("Function must return a string.");
        }
        break;
      case TYPE_BOOL:
        if (lastOpcode != OP_TRUE && lastOpcode != OP_FALSE && 
            lastOpcode != OP_EQUAL && lastOpcode != OP_GREATER && 
            lastOpcode != OP_LESS && lastOpcode != OP_NOT) {
          error("Function must return a boolean.");
        }
        break;
      case TYPE_VOID:
        // this case is handled above
        break;
      case TYPE_NONE:
        // no type checking required for TYPE_NONE
        break;
    }
    
    emitByte(OP_RETURN);
  }
}

static void whileStatement() {
  int loopStart = currentChunk()->count;
  consume(TOKEN_LEFT_PAREN, "Expect '(' after 'while'.");
  expression();
  consume(TOKEN_RIGHT_PAREN, "Expect ')' after condition.");

  int exitJump = emitJump(OP_JUMP_IF_FALSE);
  emitByte(OP_POP);
  statement();
  emitLoop(loopStart);

  patchJump(exitJump);
  emitByte(OP_POP);
}

static void synchronize() {
  parser.panicMode = false;

  while (parser.current.type != TOKEN_EOF) {
    if (parser.previous.type == TOKEN_SEMICOLON) return;
    switch (parser.current.type) {
      case TOKEN_CLASS:
      case TOKEN_FN:
      case TOKEN_VAR:
      case TOKEN_FOR:
      case TOKEN_IF:
      case TOKEN_WHILE:
      case TOKEN_OUT:
      case TOKEN_RETURN:
      case TOKEN_IMPORT:
        return;
      default:
        ; // do nothing
    }

    advance();
  }
}

static void declaration() {
  if (match(TOKEN_CLASS)) {
    classDeclaration();
  } else if (match(TOKEN_FN)) {
    fnDeclaration();
  } else if (match(TOKEN_VAR)) {
    varDeclaration();
  } else if (match(TOKEN_IMPORT)) {
    importDeclaration();
  } else {
    statement();
  }

  if (parser.panicMode) synchronize();
}

static void statement() {
  if (match(TOKEN_OUT)) {
    outStatement();
  } else if (match(TOKEN_FOR)) {
    forStatement();
  } else if (match(TOKEN_IF)) {
    ifStatement();
  } else if (match(TOKEN_RETURN)) {
    returnStatement();
  } else if (match(TOKEN_WHILE)) {
    whileStatement();
  } else if (match(TOKEN_LEFT_BRACE)) {
    beginScope();
    block();
    endScope();
  } else {
    expressionStatement();
  }
}

ObjFunction* compile(const char* source) {
  initScanner(source);
  Compiler compiler;
  initCompiler(&compiler, TYPE_SCRIPT);

  parser.hadError = false;
  parser.panicMode = false;

  advance();
  
  while (!match(TOKEN_EOF)) {
    declaration();
  }

  ObjFunction* function = endCompiler();
  return parser.hadError ? NULL : function;
}

void markCompilerRoots() {
  Compiler* compiler = current;
  while (compiler != NULL) {
    markObject((Obj*)compiler->function);
    compiler = compiler->enclosing;
  }
}
