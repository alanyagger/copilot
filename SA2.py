import sys
import csv
import os
import random
from enum import Enum
from typing import List, Dict, Optional, Union, Any, Tuple
from Scan import TokenType, tokenize

# AST节点类型
class ASTNodeType(Enum):
    PROGRAM = "Program"
    DECLARATION_LIST = "DeclarationList"
    VARIABLE_DECLARATION = "VariableDeclaration"
    FUNCTION_DECLARATION = "FunctionDeclaration"
    TYPE = "Type"
    PARAMETER = "Parameter"
    PARAMETER_LIST = "ParameterList"
    COMPOUND_STATEMENT = "CompoundStatement"
    STATEMENT_LIST = "StatementList"
    EXPRESSION_STATEMENT = "ExpressionStatement"
    IF_STATEMENT = "IfStatement"
    WHILE_STATEMENT = "WhileStatement"
    RETURN_STATEMENT = "ReturnStatement"
    ASSIGNMENT_EXPRESSION = "AssignmentExpression"
    ARRAY_SUBSCRIPT_EXPRESSION = "ArraySubscriptExpression"
    FUNCTION_CALL_EXPRESSION = "FunctionCallExpression"
    BINARY_EXPRESSION = "BinaryExpression"
    IDENTIFIER = "Identifier"
    LITERAL = "Literal"
    ARGUMENT_LIST = "ArgumentList"

# 符号表条目类型
class SymbolType(Enum):
    VARIABLE = "variable"
    ARRAY = "array"
    FUNCTION = "function"
    PARAMETER = "parameter"

# 符号表条目
class SymbolTableEntry:
    def __init__(self, name: str, symbol_type: SymbolType, data_type: str, 
                 scope_level: int, array_size: Optional[int] = None, 
                 params: Optional[List[Dict]] = None):
        self.name = name
        self.symbol_type = symbol_type
        self.data_type = data_type
        self.scope_level = scope_level
        self.array_size = array_size
        self.params = params if params else []

    def __str__(self):
        if self.symbol_type == SymbolType.ARRAY:
            return f"{self.name}: {self.data_type}[{self.array_size}] (scope: {self.scope_level})"
        elif self.symbol_type == SymbolType.FUNCTION:
            params = ", ".join([f"{p['type']} {p['name']}" for p in self.params])
            return f"{self.name}: {self.data_type}({params}) (scope: {self.scope_level})"
        else:
            return f"{self.name}: {self.data_type} (scope: {self.scope_level})"

# 符号表
class SymbolTable:
    def __init__(self):
        self.scope_level = 0
        self.table: Dict[int, Dict[str, SymbolTableEntry]] = {0: {}}
    
    def enter_scope(self):
        self.scope_level += 1
        self.table[self.scope_level] = {}
    
    def exit_scope(self):
        if self.scope_level > 0:
            del self.table[self.scope_level]
            self.scope_level -= 1
    
    def add_symbol(self, name: str, symbol_type: SymbolType, data_type: str, 
                   array_size: Optional[int] = None, params: Optional[List[Dict]] = None) -> bool:
        if name in self.table[self.scope_level]:
            return False  # 重复声明
        
        self.table[self.scope_level][name] = SymbolTableEntry(
            name, symbol_type, data_type, self.scope_level, array_size, params
        )
        return True
    
    def lookup(self, name: str) -> Optional[SymbolTableEntry]:
        for level in range(self.scope_level, -1, -1):
            if name in self.table[level]:
                return self.table[level][name]
        return None
    
    def __str__(self):
        result = []
        for level in sorted(self.table.keys()):
            result.append(f"Scope Level {level}:")
            for name, entry in self.table[level].items():
                result.append(f"  {entry}")
        return "\n".join(result)

# AST节点
class ASTNode:
    def __init__(self, node_type: ASTNodeType, value: Optional[str] = None, 
                 children: Optional[List['ASTNode']] = None, data_type: Optional[str] = None):
        self.node_type = node_type
        self.value = value
        self.children = children if children else []
        self.data_type = data_type  # 用于类型检查和推导
    
    def add_child(self, child: 'ASTNode'):
        self.children.append(child)
    
    def __str__(self, level: int = 0) -> str:
        ret = "  " * level + f"{self.node_type.value}"
        if self.value:
            ret += f": {self.value}"
        if self.data_type:
            ret += f" (type: {self.data_type})"
        ret += "\n"
        for child in self.children:
            ret += child.__str__(level + 1)
        return ret

# 语义错误
class SemanticError(Exception):
    def __init__(self, message: str, line: Optional[int] = None):
        self.message = message
        self.line = line
        super().__init__(f"Semantic Error{' at line ' + str(line) if line else ''}: {message}")

# SLR分析表加载
class SLRTable:
    def __init__(self, filename: str):
        self.actions: Dict[int, Dict[str, str]] = {}
        self.gotos: Dict[int, Dict[str, int]] = {}
        self.productions: List[Tuple[str, List[str]]] = []
        self._load_table(filename)

    def _load_table(self, filename: str):
        with open(filename, 'r') as f:
            reader = csv.DictReader(f)
            for row in reader:
                state = int(row['State'])
                self.actions[state] = {}
                self.gotos[state] = {}
                
                for key, value in row.items():
                    if key == 'State':
                        continue
                    
                    if value:
                        # Handle terminal symbols (ACTION table)
                        if key in ['ID', 'INT_NUM', 'FLOAT_NUM', 'INT', 'FLOAT', 'VOID', 
                                'IF', 'ELSE', 'WHILE', 'RETURN', 'LPAR', 'RPAR', 'LBR', 
                                'RBR', 'LBRACK', 'RBRACK', 'SEMI', 'COMMA', 'ADD', 
                                'MUL', 'ASG', 'REL_OP', 'END']:
                            self.actions[state][key] = value
                        # Handle non-terminal symbols (GOTO table)
                        else:
                            if value.isdigit():
                                self.gotos[state][key] = int(value)

# 语义分析器
class SemanticAnalyzer:
    def __init__(self, slr_table: SLRTable, grammar_file: str):
        self.slr_table = slr_table
        self._load_grammar(grammar_file)
        self.symbol_table = SymbolTable()
        self.current_scope_level = 0
        self.semantic_errors: List[str] = []
    
    def _load_grammar(self, grammar_file: str):
        self.productions = []
        with open(grammar_file, 'r') as f:
            for line in f:
                line = line.strip()
                if line and '->' in line:
                    left, right = line.split('->')
                    left = left.strip()
                    right_parts = [part.strip() for part in right.split('|')]
                    for part in right_parts:
                        symbols = part.split()
                        self.productions.append((left, symbols))
    
    def _get_action(self, state: int, token_type: str) -> str:
        if token_type in self.slr_table.actions[state]:
            return self.slr_table.actions[state][token_type]
        return ''
    
    def _get_goto(self, state: int, non_terminal: str) -> int:
        return self.slr_table.gotos[state].get(non_terminal, -1)
    
    def _token_type_to_str(self, token_type: TokenType) -> str:
        return token_type.name
    
    def analyze(self, tokens: List[Tuple[TokenType, str]]) -> ASTNode:
        print("\n=== Token Stream ===")
        for token_type, lexeme in tokens:
            print(f"<{token_type.name}, '{lexeme}'>")
        print("===================\n")

        stack = [0]  # 状态栈
        node_stack = []  # 节点栈
        token_index = 0
        # tokens.append((TokenType.END, '$'))  # 添加结束标记
        
        while True:
            current_state = stack[-1]
            current_token_type, current_lexeme = tokens[token_index]
            token_str = self._token_type_to_str(current_token_type)
            
            action = self._get_action(current_state, token_str)
            print(f"State: {current_state}, Token: {token_str}, Action: {action}")
            print(f"Stack: {stack}")
            print(f"Node Stack: {[node.node_type.value for node in node_stack]}")
            
            if not action:
                # 错误恢复尝试
                if token_str == 'SEMI' or token_str == 'RBR':
                    token_index += 1
                    continue
                else:
                    raise SyntaxError(f"Syntax error at token {current_lexeme} (type: {token_str})")
            
            if action == 'acc':
                if len(node_stack) == 1:
                    return node_stack[0]
                else:
                    raise SyntaxError("Invalid AST structure at acceptance")
            
            elif action.startswith('s'):
                # 移进
                next_state = int(action[1:])
                stack.append(next_state)
                
                # 创建叶子节点
                if token_str in ['ID', 'INT_NUM', 'FLOAT_NUM']:
                    node_type = {
                        'ID': ASTNodeType.IDENTIFIER,
                        'INT_NUM': ASTNodeType.LITERAL,
                        'FLOAT_NUM': ASTNodeType.LITERAL
                    }[token_str]
                    node = ASTNode(node_type, current_lexeme)
                    if token_str in ['INT_NUM', 'FLOAT_NUM']:
                        node.data_type = 'int' if token_str == 'INT_NUM' else 'float'
                else:
                    node = ASTNode(ASTNodeType.LITERAL, current_lexeme)
                
                node_stack.append(node)
                token_index += 1
            
            elif action.startswith('r'):
                # 归约
                production_index = int(action[1:])
                left, right = self.productions[production_index]
                print(f"Reducing by production: {left} -> {' '.join(right)}")
                
                if right != ['ε']:
                    for _ in range(len(right)):
                        stack.pop()
                
                current_state = stack[-1]
                next_state = self._get_goto(current_state, left)
                stack.append(next_state)
                
                new_node = self._apply_semantic_action(left, right, node_stack)
                node_stack.append(new_node)
            
            else:
                raise RuntimeError(f"Invalid action: {action}")
            print('\n')
    
    def _apply_semantic_action(self, left: str, right: List[str], node_stack: List[ASTNode]) -> ASTNode:
        popped_nodes = []
        if right != ['ε']:
            for _ in range(len(right)):
                popped_nodes.insert(0, node_stack.pop())
        
        node_type = {
            'Prog': ASTNodeType.PROGRAM,
            'DeclList': ASTNodeType.DECLARATION_LIST,
            'Decl': ASTNodeType.DECLARATION_LIST,
            'VarDecl': ASTNodeType.VARIABLE_DECLARATION,
            'Type': ASTNodeType.TYPE,
            'FunDecl': ASTNodeType.FUNCTION_DECLARATION,
            'ParamList': ASTNodeType.PARAMETER_LIST,
            'Param': ASTNodeType.PARAMETER,
            'CompStmt': ASTNodeType.COMPOUND_STATEMENT,
            'StmtList': ASTNodeType.STATEMENT_LIST,
            'Stmt': None,
            'ExprStmt': ASTNodeType.EXPRESSION_STATEMENT,
            'IfStmt': ASTNodeType.IF_STATEMENT,
            'LoopStmt': ASTNodeType.WHILE_STATEMENT,
            'RetStmt': ASTNodeType.RETURN_STATEMENT,
            'Expr': None,
            'SimpExpr': None,
            'AddExpr': None,
            'Term': None,
            'Fact': None,
            'ArgList': ASTNodeType.ARGUMENT_LIST
        }.get(left)
        
        if left == 'Prog':
            return ASTNode(ASTNodeType.PROGRAM, children=popped_nodes)
        
        elif left == 'DeclList' and right == ['DeclList', 'Decl']:
            popped_nodes[0].children.extend(popped_nodes[1].children)
            return popped_nodes[0]
        
        elif left == 'DeclList' and right == ['Decl']:
            new_node = ASTNode(ASTNodeType.DECLARATION_LIST, children=popped_nodes)
            return new_node
        
        elif left == 'Decl' and right[0] in ['VarDecl', 'FunDecl']:
            return popped_nodes[0]
        
        elif left == 'VarDecl' and right == ['Type', 'ID', 'SEMI']:
            type_node, id_node, _ = popped_nodes
            var_name = id_node.value
            var_type = type_node.value
            
            if not self.symbol_table.add_symbol(var_name, SymbolType.VARIABLE, var_type):
                self.semantic_errors.append(f"Duplicate declaration of variable '{var_name}'")
            
            new_node = ASTNode(ASTNodeType.VARIABLE_DECLARATION, children=popped_nodes[:2])
            new_node.data_type = var_type
            return new_node
        
        elif left == 'VarDecl' and right == ['Type', 'ID', 'LBRACK', 'INT_NUM', 'RBRACK', 'SEMI']:
            type_node, id_node, _, int_node, _, _ = popped_nodes
            var_name = id_node.value
            var_type = type_node.value
            array_size = int(int_node.value)
            
            if not self.symbol_table.add_symbol(var_name, SymbolType.ARRAY, var_type, array_size):
                self.semantic_errors.append(f"Duplicate declaration of array '{var_name}'")
            
            new_node = ASTNode(ASTNodeType.VARIABLE_DECLARATION, children=[type_node, id_node, int_node])
            new_node.data_type = f"{var_type}[{array_size}]"
            return new_node
        
        elif left == 'VarDecl' and right == ['Type', 'ID', 'ASG', 'Expr', 'SEMI']:
            type_node, id_node, _, expr_node, _ = popped_nodes
            var_name = id_node.value
            var_type = type_node.value
            
            if expr_node.data_type != var_type:
                self.semantic_errors.append(
                    f"Type mismatch in initialization: '{var_name}' is {var_type}, "
                    f"but expression is {expr_node.data_type}"
                )
            
            if not self.symbol_table.add_symbol(var_name, SymbolType.VARIABLE, var_type):
                self.semantic_errors.append(f"Duplicate declaration of variable '{var_name}'")
            
            new_node = ASTNode(
                ASTNodeType.VARIABLE_DECLARATION, 
                children=[type_node, id_node, expr_node]
            )
            new_node.data_type = var_type
            return new_node
        
        elif left == 'Type' and right[0] in ['INT', 'FLOAT', 'VOID']:
            type_node = popped_nodes[0]
            new_node = ASTNode(ASTNodeType.TYPE, type_node.value)
            new_node.data_type = type_node.value
            return new_node
        
        elif left == 'FunDecl' and right == ['Type', 'ID', 'LPAR', 'ParamList', 'RPAR', 'CompStmt']:
            type_node, id_node, _, param_list_node, _, comp_stmt_node = popped_nodes
            func_name = id_node.value
            return_type = type_node.value
            
            params = []
            for param_node in param_list_node.children:
                param_type = param_node.children[0].value
                param_name = param_node.children[1].value
                is_array = len(param_node.children) > 2
                
                param_info = {
                    'type': param_type,
                    'name': param_name,
                    'is_array': is_array
                }
                params.append(param_info)
            
            if not self.symbol_table.add_symbol(
                func_name, SymbolType.FUNCTION, return_type, params=params
            ):
                self.semantic_errors.append(f"Duplicate declaration of function '{func_name}'")
            
            self.symbol_table.enter_scope()
            
            for param in params:
                symbol_type = SymbolType.ARRAY if param['is_array'] else SymbolType.PARAMETER
                self.symbol_table.add_symbol(
                    param['name'], symbol_type, param['type']
                )
            
            new_node = ASTNode(
                ASTNodeType.FUNCTION_DECLARATION,
                children=[type_node, id_node, param_list_node, comp_stmt_node]
            )
            new_node.data_type = return_type
            
            self.symbol_table.exit_scope()
            
            return new_node
        
        elif left == 'ParamList' and right == ['ParamList', 'COMMA', 'Param']:
            popped_nodes[0].add_child(popped_nodes[2])
            return popped_nodes[0]
        
        elif left == 'ParamList' and right == ['Param']:
            new_node = ASTNode(ASTNodeType.PARAMETER_LIST, children=[popped_nodes[0]])
            return new_node
        
        elif left == 'ParamList' and right == ['ε']:
            return ASTNode(ASTNodeType.PARAMETER_LIST)
        
        elif left == 'Param' and right == ['Type', 'ID']:
            type_node, id_node = popped_nodes
            new_node = ASTNode(ASTNodeType.PARAMETER, children=popped_nodes)
            new_node.data_type = type_node.value
            return new_node
        
        elif left == 'Param' and right == ['Type', 'ID', 'LBRACK', 'RBRACK']:
            type_node, id_node, _, _ = popped_nodes
            new_node = ASTNode(ASTNodeType.PARAMETER, children=[type_node, id_node])
            new_node.data_type = f"{type_node.value}[]"
            return new_node
        
        elif left == 'CompStmt' and right == ['LBR', 'StmtList', 'RBR']:
            self.symbol_table.enter_scope()
            stmt_list_node = popped_nodes[1]
            self.symbol_table.exit_scope()
            
            new_node = ASTNode(ASTNodeType.COMPOUND_STATEMENT, children=[stmt_list_node])
            return new_node
        
        elif left == 'StmtList' and right == ['StmtList', 'Stmt']:
            popped_nodes[0].add_child(popped_nodes[1])
            return popped_nodes[0]
        
        elif left == 'StmtList' and right == ['ε']:
            return ASTNode(ASTNodeType.STATEMENT_LIST)
        
        elif left == 'Stmt' and right[0] in ['VarDecl', 'OtherStmt']:
            return popped_nodes[0]
        
        elif left == 'OtherStmt' and right[0] in ['ExprStmt', 'CompStmt', 'IfStmt', 'LoopStmt', 'RetStmt']:
            return popped_nodes[0]
        
        elif left == 'ExprStmt' and right == ['Expr', 'SEMI']:
            new_node = ASTNode(ASTNodeType.EXPRESSION_STATEMENT, children=[popped_nodes[0]])
            new_node.data_type = popped_nodes[0].data_type
            return new_node
        
        elif left == 'ExprStmt' and right == ['SEMI']:
            return ASTNode(ASTNodeType.EXPRESSION_STATEMENT)
        
        elif left == 'IfStmt' and right == ['IF', 'LPAR', 'Expr', 'RPAR', 'CompStmt']:
            _, _, expr_node, _, comp_stmt_node = popped_nodes
            
            if expr_node.data_type != 'bool':
                self.semantic_errors.append(
                    f"Condition in if statement must be boolean, got {expr_node.data_type}"
                )
            
            new_node = ASTNode(ASTNodeType.IF_STATEMENT, children=[expr_node, comp_stmt_node])
            return new_node
        
        elif left == 'IfStmt' and right == ['IF', 'LPAR', 'Expr', 'RPAR', 'CompStmt', 'ELSE', 'CompStmt']:
            _, _, expr_node, _, if_comp_stmt, _, else_comp_stmt = popped_nodes
            
            if expr_node.data_type != 'bool':
                self.semantic_errors.append(
                    f"Condition in if-else statement must be boolean, got {expr_node.data_type}"
                )
            
            new_node = ASTNode(
                ASTNodeType.IF_STATEMENT, 
                children=[expr_node, if_comp_stmt, else_comp_stmt]
            )
            return new_node
        
        elif left == 'LoopStmt' and right == ['WHILE', 'LPAR', 'Expr', 'RPAR', 'Stmt']:
            _, _, expr_node, _, stmt_node = popped_nodes
            
            if expr_node.data_type != 'bool':
                self.semantic_errors.append(
                    f"Condition in while loop must be boolean, got {expr_node.data_type}"
                )
            
            new_node = ASTNode(ASTNodeType.WHILE_STATEMENT, children=[expr_node, stmt_node])
            return new_node
        
        elif left == 'RetStmt' and right == ['RETURN', 'Expr', 'SEMI']:
            _, expr_node, _ = popped_nodes
            
            new_node = ASTNode(ASTNodeType.RETURN_STATEMENT, children=[expr_node])
            new_node.data_type = expr_node.data_type
            return new_node
        
        elif left == 'RetStmt' and right == ['RETURN', 'SEMI']:
            return ASTNode(ASTNodeType.RETURN_STATEMENT)
        
        elif left == 'Expr' and right == ['ID', 'ASG', 'Expr']:
            id_node, _, expr_node = popped_nodes
            var_name = id_node.value
            
            symbol = self.symbol_table.lookup(var_name)
            if not symbol:
                self.semantic_errors.append(f"Undeclared variable '{var_name}'")
            else:
                if symbol.data_type != expr_node.data_type:
                    self.semantic_errors.append(
                        f"Type mismatch in assignment: '{var_name}' is {symbol.data_type}, "
                        f"but expression is {expr_node.data_type}"
                    )
            
            new_node = ASTNode(
                ASTNodeType.ASSIGNMENT_EXPRESSION, 
                value='=', 
                children=[id_node, expr_node]
            )
            new_node.data_type = expr_node.data_type
            return new_node
        
        elif left == 'Expr' and right == ['ID', 'LBRACK', 'Expr', 'RBRACK', 'ASG', 'Expr']:
            id_node, _, index_expr, _, _, value_expr = popped_nodes
            var_name = id_node.value
            
            symbol = self.symbol_table.lookup(var_name)
            if not symbol:
                self.semantic_errors.append(f"Undeclared array '{var_name}'")
            elif symbol.symbol_type != SymbolType.ARRAY:
                self.semantic_errors.append(f"'{var_name}' is not an array")
            else:
                if index_expr.data_type != 'int':
                    self.semantic_errors.append(
                        f"Array index must be integer, got {index_expr.data_type}"
                    )
                
                if symbol.data_type != value_expr.data_type:
                    self.semantic_errors.append(
                        f"Type mismatch in array assignment: '{var_name}' is {symbol.data_type}, "
                        f"but expression is {value_expr.data_type}"
                    )
            
            new_node = ASTNode(
                ASTNodeType.ASSIGNMENT_EXPRESSION,
                value='=[]',
                children=[id_node, index_expr, value_expr]
            )
            new_node.data_type = value_expr.data_type
            return new_node
        
        elif left == 'Expr' and right == ['ID', 'LPAR', 'ArgList', 'RPAR']:
            id_node, _, arg_list_node, _ = popped_nodes
            func_name = id_node.value
            
            symbol = self.symbol_table.lookup(func_name)
            if not symbol:
                self.semantic_errors.append(f"Undeclared function '{func_name}'")
            elif symbol.symbol_type != SymbolType.FUNCTION:
                self.semantic_errors.append(f"'{func_name}' is not a function")
            else:
                if len(arg_list_node.children) != len(symbol.params):
                    self.semantic_errors.append(
                        f"Function '{func_name}' expects {len(symbol.params)} arguments, "
                        f"got {len(arg_list_node.children)}"
                    )
                else:
                    for i, (arg_node, param) in enumerate(zip(arg_list_node.children, symbol.params)):
                        if arg_node.data_type != param['type']:
                            self.semantic_errors.append(
                                f"Argument {i+1} type mismatch in call to '{func_name}': "
                                f"expected {param['type']}, got {arg_node.data_type}"
                            )
            
            new_node = ASTNode(
                ASTNodeType.FUNCTION_CALL_EXPRESSION,
                children=[id_node, arg_list_node]
            )
            new_node.data_type = symbol.data_type if symbol else 'unknown'
            return new_node
        
        elif left == 'Expr' and right == ['SimpExpr']:
            return popped_nodes[0]
        
        elif left == 'SimpExpr' and right == ['AddExpr', 'REL_OP', 'AddExpr']:
            left_expr, op_node, right_expr = popped_nodes
            
            if left_expr.data_type != right_expr.data_type:
                self.semantic_errors.append(
                    f"Operand type mismatch in relational expression: "
                    f"{left_expr.data_type} {op_node.value} {right_expr.data_type}"
                )
            
            new_node = ASTNode(
                ASTNodeType.BINARY_EXPRESSION,
                value=op_node.value,
                children=[left_expr, right_expr]
            )
            new_node.data_type = 'bool'
            return new_node
        
        elif left == 'SimpExpr' and right == ['AddExpr']:
            return popped_nodes[0]
        
        elif left == 'AddExpr' and right == ['AddExpr', 'ADD', 'Term']:
            left_expr, op_node, right_expr = popped_nodes
            
            if left_expr.data_type != right_expr.data_type:
                self.semantic_errors.append(
                    f"Operand type mismatch in addition: "
                    f"{left_expr.data_type} + {right_expr.data_type}"
                )
            
            new_node = ASTNode(
                ASTNodeType.BINARY_EXPRESSION,
                value=op_node.value,
                children=[left_expr, right_expr]
            )
            new_node.data_type = left_expr.data_type
            return new_node
        
        elif left == 'AddExpr' and right == ['Term']:
            return popped_nodes[0]
        
        elif left == 'Term' and right == ['Term', 'MUL', 'Fact']:
            left_expr, op_node, right_expr = popped_nodes
            
            if left_expr.data_type != right_expr.data_type:
                self.semantic_errors.append(
                    f"Operand type mismatch in multiplication: "
                    f"{left_expr.data_type} * {right_expr.data_type}"
                )
            
            new_node = ASTNode(
                ASTNodeType.BINARY_EXPRESSION,
                value=op_node.value,
                children=[left_expr, right_expr]
            )
            new_node.data_type = left_expr.data_type
            return new_node
        
        elif left == 'Term' and right == ['Fact']:
            return popped_nodes[0]
        
        elif left == 'Fact' and right == ['ID']:
            id_node = popped_nodes[0]
            var_name = id_node.value
            
            symbol = self.symbol_table.lookup(var_name)
            if not symbol:
                self.semantic_errors.append(f"Undeclared variable '{var_name}'")
                id_node.data_type = 'unknown'
            else:
                id_node.data_type = symbol.data_type
            
            return id_node
        
        elif left == 'Fact' and right == ['ID', 'LBRACK', 'Expr', 'RBRACK']:
            id_node, _, index_expr, _ = popped_nodes
            var_name = id_node.value
            
            symbol = self.symbol_table.lookup(var_name)
            if not symbol:
                self.semantic_errors.append(f"Undeclared array '{var_name}'")
                data_type = 'unknown'
            elif symbol.symbol_type != SymbolType.ARRAY:
                self.semantic_errors.append(f"'{var_name}' is not an array")
                data_type = 'unknown'
            else:
                if index_expr.data_type != 'int':
                    self.semantic_errors.append(
                        f"Array index must be integer, got {index_expr.data_type}"
                    )
                data_type = symbol.data_type
            
            new_node = ASTNode(
                ASTNodeType.ARRAY_SUBSCRIPT_EXPRESSION,
                children=[id_node, index_expr]
            )
            new_node.data_type = data_type
            return new_node
        
        elif left == 'Fact' and right in [['INT_NUM'], ['FLOAT_NUM']]:
            return popped_nodes[0]
        
        elif left == 'Fact' and right == ['LPAR', 'Expr', 'RPAR']:
            return popped_nodes[1]
        
        elif left == 'ArgList' and right == ['ArgList', 'COMMA', 'Expr']:
            popped_nodes[0].add_child(popped_nodes[2])
            return popped_nodes[0]
        
        elif left == 'ArgList' and right == ['Expr']:
            new_node = ASTNode(ASTNodeType.ARGUMENT_LIST, children=[popped_nodes[0]])
            return new_node
        
        elif left == 'ArgList' and right == ['ε']:
            return ASTNode(ASTNodeType.ARGUMENT_LIST)
        
        else:
            new_node = ASTNode(
                ASTNodeType(node_type.value) if node_type else ASTNode(ASTNodeType.LITERAL),
                children=popped_nodes
            )
            return new_node

def main():
    # 创建输出目录
    os.makedirs("output", exist_ok=True)
    
    # 1. 加载SLR分析表
    slr_table = SLRTable("slr_table.csv")
    
    # 2. 创建语义分析器
    analyzer = SemanticAnalyzer(slr_table, "mainGG.txt")
    
    # 3. 从代码库中随机选择一个文件
    codebase_dir = "代码库"
    if not os.path.exists(codebase_dir):
        print(f"Error: Codebase directory '{codebase_dir}' not found.")
        return
    
    src_files = [f for f in os.listdir(codebase_dir) if f.endswith('.src')]
    if not src_files:
        print(f"No .src files found in '{codebase_dir}'")
        return
    
    # selected_file = random.choice(src_files)
    selected_file = "22.src"  # For testing, use a specific file
    input_file = os.path.join(codebase_dir, selected_file)
    print(f"\nSelected file for analysis: {input_file}")
    
    # 4. 读取输入文件并生成token流
    with open(input_file, 'r') as f:
        source_code = f.read()
    
    tokens = tokenize(source_code)
    
    # 5. 进行语义分析
    try:
        ast = analyzer.analyze(tokens)
        
        # 输出AST
        print("\nAbstract Syntax Tree (AST):")
        print(ast)
        
        # 输出符号表
        print("\nSymbol Table:")
        print(analyzer.symbol_table)
        
        # 输出语义错误
        if analyzer.semantic_errors:
            print("\nSemantic Errors:")
            for error in analyzer.semantic_errors:
                print(f"- {error}")
        else:
            print("\nNo semantic errors found.")
        
        # 6. 保存结果到文件
        base_name = os.path.splitext(selected_file)[0]
        output_prefix = os.path.join("output", base_name)
        
        # 保存AST
        ast_file = f"{output_prefix}_ast.txt"
        with open(ast_file, 'w') as f:
            f.write(str(ast))
        print(f"\nAST saved to: {ast_file}")
        
        # 保存符号表
        symtab_file = f"{output_prefix}_symtab.txt"
        with open(symtab_file, 'w') as f:
            f.write(str(analyzer.symbol_table))
        print(f"Symbol table saved to: {symtab_file}")
        
        # 保存语义错误（如果有）
        if analyzer.semantic_errors:
            error_file = f"{output_prefix}_errors.txt"
            with open(error_file, 'w') as f:
                f.write("\n".join(analyzer.semantic_errors))
            print(f"Semantic errors saved to: {error_file}")
            
    except Exception as e:
        print(f"Error during semantic analysis: {e}")

if __name__ == "__main__":
    main()