from collections import defaultdict
from libcst import Assert, Assign, Attribute, BooleanOperation, CSTVisitor, Call, Comparison, Expr, FunctionDef, Index, Name, SimpleString, Subscript
from libcst.display import dump

from agent.logic.forge.logic_py_forge_constraint_generator import ForgeAttributeAccess, ForgeConstraint, ForgeExpr, ForgeFunctionLookup, ForgeOperator, ForgePredicateCall, ForgeSymbol, LogicPyForgeConstraintGenerator
from agent.logic.forge.logic_py_forge_data_structure_generator import LogicPyForgeDataStructureMetadata

class LogicPyForgeConstraintGeneratorMigrate(CSTVisitor):
    def __init__(self, data_structure_metadata: LogicPyForgeDataStructureMetadata):
        super().__init__()
        self.constraints: list[ForgeExpr] = [] # List of all constraints found maintained in the order of the definition in Forge
        self.types_to_vars: defaultdict[str, list[str]] = defaultdict(list) # type_name -> nondet var name
        self.vars_to_constraints: dict[str, list[ForgeExpr]] = {} # var_name (can be nondet or regular) -> list of asserts and assumes
        self.forge_code = ""
        self.__cur_var = ""
        self.data_structure_metadata = data_structure_metadata

    def visit_FunctionDef(self, node: FunctionDef):
        # Only visit function called "validate"
        if node.name.value == "validate":
            node.body.visit(self)
    
    def visit_Assign(self, node: Assign):
        # Retrieve the target
        targets = node.targets
        value = node.value
        if value and isinstance(value, Call) and isinstance(value.func, Name) and value.func.value == "nondet":
            # It's a nondet assignment
            nondet_var_name = targets[0].target.value
            if not isinstance(nondet_var_name, str): 
                raise ValueError("Nondet variable name is not a string.")
            self.__cur_var = nondet_var_name
            _, nondet_source = self.parse_Call(value)

            # Get the source field being assigned to the nondet variable
            nondet_source_expr = self._expr_to_forge(nondet_source[0]) # e.g., "solution.volcanologist"
            if not isinstance(nondet_source_expr, ForgeAttributeAccess):
                raise ValueError("Nondet source expression is not an attribute access.")

            # Add nondet var to class metadata
            type_name = self.get_ds_class_field_type(nondet_source_expr)
            self.types_to_vars[type_name].append(nondet_var_name)

            if nondet_var_name not in self.vars_to_constraints:
                self.vars_to_constraints[nondet_var_name] = []
        else:
            # Handle a generic assignment
            var_name = targets[0].target.value
            if not isinstance(var_name, str): 
                raise ValueError("Assigned variable name is not a string.")
            self.__cur_var = var_name # FIXME: Remove the assumption that a current variable is always set (via a nondet or regular assignment)

            if var_name not in self.vars_to_constraints:
                self.vars_to_constraints[var_name] = []

            # Evaluate the RHS
            if value and isinstance(value, Subscript):
                function, index = self.parse_Subscript(value)

                # Retrieve the variable's type
                if isinstance(function, ForgeAttributeAccess):
                    type_name = self.get_ds_class_field_type(function)
                    self.types_to_vars[type_name].append(var_name)
                else:
                    raise ValueError("Assigned function is not an attribute access.")
                rhs = ForgeFunctionLookup(function=self._forge_constraint_to_str(function), key=str(index))

            constraint = ForgeConstraint(operator=ForgeOperator.EQUALS, lhs=ForgeSymbol(name=var_name), rhs=rhs)
            self.constraints.append(constraint)
            self.vars_to_constraints[self.__cur_var].append(constraint)
    
    def vist_Expr(self, node: Expr):
        # Assume statements
        assume_call = node.value
        assume_arg = assume_call.args[0].value
        if isinstance(assume_arg, Comparison): # FIXME: Left off here
            left = self._expr_to_forge(assume_arg.left)
            right = self._expr_to_forge(assume_arg.comparisons[0].comparator)

            constraint = ForgeConstraint(operator=ForgeOperator.EQUALS, lhs=left, rhs=right)
            self.constraints.append(constraint)
            self.vars_to_constraints[self.__cur_var].append(constraint)
            
        # NOTE: handle other operators with assume HERE

    def visit_Assert(self, node: Assert):
        assert_stmt = node.test

        # Handle `immediatelyBefore` helper call
        if assert_stmt and isinstance(assert_stmt, Call):
            predicate, params = self.parse_Call(assert_stmt)
            if predicate and params:
                constraint = ForgePredicateCall(predicate=predicate, params=params)
                self.constraints.append(constraint)
                # self.vars_to_constraints[self.__cur_var].append(constraint)
        
        # Handle `or` expressions
        elif isinstance(assert_stmt, BooleanOperation) and isinstance(assert_stmt.operator, Or):
            left = assert_stmt.left
            right = assert_stmt.right
            left_predicate, left_params = self.parse_Call(left)
            right_predicate, right_params = self.parse_Call(right)
            if left_predicate and left_params and right_predicate and right_params:
                lhs = ForgePredicateCall(predicate=left_predicate, params=left_params)
                rhs = ForgePredicateCall(predicate=right_predicate, params=right_params)
                constraint = ForgeConstraint(operator=ForgeOperator.OR, lhs=lhs, rhs=rhs)
                self.constraints.append(constraint)
                # self.vars_to_constraints[self.__cur_var].append(constraint)

        # Handle `Comparision`
        elif isinstance(assert_stmt, Comparison):
            print("Comparison found in assert statement.", dump(assert_stmt))
            left = self._expr_to_forge(expr=assert_stmt.left)
            right = self._expr_to_forge(expr=assert_stmt.comparisons[0].comparator)

            constraint = ForgeConstraint(operator=ForgeOperator.EQUALS, lhs=left, rhs=right)
            self.constraints.append(constraint)
            # self.vars_to_constraints[self.__cur_var].append(constraint)

        else:
            print("Unhandled branch within an assert statement:", dump(assert_stmt))

    def _expr_to_forge(self, expr) -> ForgeExpr:
        """
        Converts a CST expression to a ForgeExpr object.
        """

        # Simplified: handle Name, Attribute, etc.
        if isinstance(expr, Name):
            return ForgeSymbol(name=str.replace(expr.value, " ", "_"))
        elif isinstance(expr, Attribute):
            return ForgeAttributeAccess(object=self._expr_to_forge(expr.value), attr_name=self._expr_to_forge(expr.attr.value))
        elif isinstance(expr, SimpleString):
            return ForgeSymbol(name=str.replace(expr.evaluated_value.capitalize(), " ", "_"))
        elif isinstance(expr, str):
            return ForgeSymbol(name=str.replace(expr.lower(), " ", "_"))
        elif isinstance(expr, Subscript):
            function, index = self.parse_Subscript(expr)
            return ForgeFunctionLookup(function=self._forge_constraint_to_str(function), key=str(index))
        else:
            raise ValueError(f"expr_to_forge: Unhandled expression type ({type(expr)}) for expression: {dump(expr)}")
        
    def _forge_constraint_to_str(self, expr: ForgeExpr) -> str:
        """
        Converts a Forge constraint to a String.
        """

        match expr:
            case ForgeConstraint(op, lhs, rhs):
                match op:
                    case ForgeOperator.EQUALS:
                        return f"{self._forge_constraint_to_str(lhs)} = {self._forge_constraint_to_str(rhs)}"
                    case ForgeOperator.OR:
                        return f"{self._forge_constraint_to_str(lhs)} or {self._forge_constraint_to_str(rhs)}"
                    case _:
                        raise ValueError("ForgeOperator enum not handled: ", op)
            case ForgePredicateCall(predicate, params):
                return f"{predicate}[{', '.join(params)}]"
            case ForgeFunctionLookup(function, key):
                return f"{function}[{key}]"
            case ForgeAttributeAccess(obj, a_n):
                return f"{self._forge_constraint_to_str(obj)}.{self._forge_constraint_to_str(a_n)}"
            case ForgeSymbol(n):
                if n.lower() == "solution":
                    return "Solution"
                return n
            case _:
                # raise ValueError("expr variant not handled:", expr)
                print("expr variant not handled:", expr)
        
    def parse_Subscript(self, node: Subscript) -> tuple[ForgeExpr, int]:
        # Assumes that the node is a Subscript
        function = self._expr_to_forge(node.value)
        slice = node.slice
        if slice and isinstance(slice[0].slice, Index):
            index = slice[0].slice.value.value
            return function, index
        else:
            raise ValueError("Slice contains non-index values. You need to add a way to handle these values.")
        
    def get_ds_field_type(self, field_name: str) -> str:
        return self.data_structure_metadata.get_field_type(field_name)
    
    def get_ds_class_field_type(self, expr: ForgeAttributeAccess) -> str:
        class_name = self._forge_constraint_to_str(expr.object)
        field_name = self._forge_constraint_to_str(expr.attr_name)

        return self.data_structure_metadata.get_class_field_type(class_name, field_name)