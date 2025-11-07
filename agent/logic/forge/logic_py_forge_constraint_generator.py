"""
Forge Constraint Generator

This module should implement the logic to convert Logic.py constraints
(e.g., assertions in premise/conclusion functions) into Forge constraints.

TODO:
- Implement the visitor pattern to traverse the CST and extract constraints.
- Map Logic.py assertions and expressions to Forge constraint syntax.
- Use metadata from the data structure generator as needed.
"""

from __future__ import annotations
import heapq
from typing import Optional # lazy evaluation of type annotations

from libcst import Assign, BooleanOperation, CSTVisitor, Call, EmptyLine, Expr, Index, MetadataWrapper, Module, FunctionDef, Assert, Comparison, Name, Attribute, Or, SimpleString, Subscript
from libcst.display import dump
from libcst.metadata import PositionProvider

from dataclasses import dataclass
from enum import Enum
from collections import defaultdict, OrderedDict

from agent.logic.forge.logic_py_forge_data_structure_generator import LogicPyForgeDataStructureMetadata

class ForgeOperator(Enum):
    EQUALS = 1
    OR = 2

class ForgeExpr:
    pass

@dataclass
class ForgeConstraint(ForgeExpr):
    operator: ForgeOperator
    lhs: ForgeExpr 
    rhs: ForgeExpr

@dataclass
class ForgePredicateCall(ForgeExpr):
    predicate: ForgeSymbol
    params: list[ForgeExpr]

@dataclass
class ForgeFunctionLookup(ForgeExpr):
    function: ForgeExpr
    key: str

@dataclass
class ForgeAttributeAccess(ForgeExpr):
    object: ForgeExpr # This needs to be a ForgeExpr (and not just a ForgeSymbol) because of this case: Solution.volcanologists.Volcano = Supervolcano
    attr_name: ForgeSymbol

# NOTE: Potentially, an issue that the ForgeSymbol represents both Python symbols and strings?
@dataclass
class ForgeSymbol(ForgeExpr):
    name: str

class LogicPyForgeConstraintGenerator(CSTVisitor):
    METADATA_DEPENDENCIES = (PositionProvider,)

    def __init__(self, data_structure_metadata: LogicPyForgeDataStructureMetadata):
        super().__init__()

        # Variables to build Forge constraints
        self.constraints: list[ForgeExpr] = [] # List of all constraints found maintained in the order of the definition in Forge
        self.types_to_vars: defaultdict[str, list[str]] = defaultdict(list) # type_name -> nondet var name
        self.vars_to_constraints: dict[str, list[ForgeExpr]] = {} # var_name (can be nondet or regular) -> list of asserts and assumes
        self.__cur_var = ""
        self.forge_code = ""

        # Store data structure metadata
        self.data_structure_metadata = data_structure_metadata

        # Temporary stack to hold intermediate visitor outputs
        # NOTE: This is necessary because libCST `visit_` functions only return an Optional[bool], not ForgeExpr's
        self._visitor_output_stack: list[ForgeExpr] = []

        # Comment tracking variables
        self.comment_heap: list[tuple[int, str]] = [] # [(line_num, comment_text), ...]
        self.current_comment: Optional[tuple[int, str]] = None
        self.comment_to_constraints: OrderedDict[tuple[int, str], list[ForgeExpr]] = OrderedDict() # (line_num, comment_text) -> [constraints]

        # Add an "Uncategorized" section to the OrderedDict
        uncategorized = (0, "")
        self.comment_to_constraints[uncategorized] = []


    """

    COMMENT HANDLING HELPERS

    """

    def __associate_constraint_with_comment(self, constraint: ForgeExpr, node):
        """
        Associate a constraint with the current comment.

        Args:
            constraint (ForgeExpr): The constraint to associate.
            node: The CST node where the constraint was found (used for position).
        """
        # Get constraint position
        position = self.get_metadata(PositionProvider, node, None)
        if not position:
            if self.current_comment:
                self.comment_to_constraints[self.current_comment].append(constraint)
            return
        
        constraint_line = position.start.line

        # Update current comment based on constraint position
        # Pop comments from heap if their line is before the constraint
        while self.comment_heap and self.comment_heap[0][0] < constraint_line:
            comment_tuple = heapq.heappop(self.comment_heap)
            self.current_comment = comment_tuple

        # Associate with current comment
        if self.current_comment:
            self.comment_to_constraints[self.current_comment].append(constraint)
        else:
            # If no current comment, associate with "Uncategorized"
            uncategorized = (0, "")
            self.comment_to_constraints[uncategorized].append(constraint)


    """

    CLASS LEVEL VISITORS

    """
    def visit_FunctionDef(self, node: FunctionDef) -> Optional[bool]:
        # Only visit function called "validate"
        if node.name.value == "validate":
            node.body.visit(self)
            return False
        


    """

    LEAF LEVEL VISITORS

    """
    def visit_Name(self, node: Name) -> Optional[bool]:
        self._visitor_output_stack.append(ForgeSymbol(name=str.replace(node.value, " ", "_")))
        return False
    
    def visit_Attribute(self, node: Attribute) -> Optional[bool]:
        node.value.visit(self)
        forge_object = self._visitor_output_stack.pop()
        node.attr.visit(self)
        forge_field = self._visitor_output_stack.pop()
        self._visitor_output_stack.append(ForgeAttributeAccess(object=forge_object, attr_name=forge_field))
        return False

    def visit_SimpleString(self, node: SimpleString) -> Optional[bool]:
        self._visitor_output_stack.append(ForgeSymbol(name=str.replace(node.evaluated_value.capitalize(), " ", "_")))
        return False
    
    def visit_Subscript(self, node: Subscript) -> Optional[bool]:
        function, index = self.parse_Subscript(node)
        self._visitor_output_stack.append(ForgeFunctionLookup(function=self._forge_constraint_to_str(function), key=str(index)))
        return False
    
    def visit_EmptyLine(self, node: EmptyLine) -> Optional[bool]:
        if node.comment is not None:
            line = self.get_metadata(PositionProvider, node)
            if not line: 
                raise ValueError("couldn't find line number for comment")
            
            line = line.start.line
            comment_text = node.comment.value.strip().lstrip('#').strip()
            comment_tuple = (line, comment_text)
            heapq.heappush(self.comment_heap, comment_tuple)
            
            # Initialize in OrderedDict - insertion order preserved
            if comment_tuple not in self.comment_to_constraints:
                self.comment_to_constraints[comment_tuple] = []
        return False

    
    """
    
    INTERMEDIATE EXPRESSION VISITORS

    """
    def visit_Call(self, node: Call) -> Optional[bool]:
        """
        Visit a call and parse the function and parameters.
        """
        func = node.func

        # NOTE: This is where the "assume" function is handled
        if isinstance(func, Name) and func.value == "assume":
            if len(node.args) > 1:
                raise ValueError(f"Too many arguments ({len(node.args)}) in a Logic.py Assume expression")
            assume_expr = node.args[0]
            assume_expr.visit(self)
            constraint = self._visitor_output_stack.pop()
            self.constraints.append(constraint)
            self.__associate_constraint_with_comment(constraint, node)
            return False

        if isinstance(func, Name) and not (func.value == "nondet" or func.value == "immediatelyBefore" or func.value == "somewhereBefore"):
            print(f"Function call {func.value} not handled")

        params: list[ForgeExpr] = []
        for arg in node.args:
            arg.value.visit(self)
            params.append(self._visitor_output_stack.pop())
        self._visitor_output_stack.append(ForgePredicateCall(predicate=func.value, params=params))

        return False
    
    def visit_Comparison(self, node: Comparison):
        # Assert that comparison is binary
        if len(node.comparisons) > 1:
            raise ValueError("Only binary comparisons are supported.")

        node.left.visit(self)
        left_expr = self._visitor_output_stack.pop()
        node.comparisons[0].comparator.visit(self)
        right_expr = self._visitor_output_stack.pop()

        # FIXME: Handle the Comparison operators correctly; convert BaseCompOp to ForgeOperator enum
        constraint = ForgeConstraint(operator=ForgeOperator.EQUALS, lhs=left_expr, rhs=right_expr)
        self._visitor_output_stack.append(constraint)

        return False

    def visit_BooleanOperation(self, node: BooleanOperation):
        node.left.visit(self)
        l_expr = self._visitor_output_stack.pop()
        left_predicate, left_params = l_expr.predicate, l_expr.params

        node.right.visit(self)
        r_expr = self._visitor_output_stack.pop()
        right_predicate, right_params = r_expr.predicate, r_expr.params

        lhs = ForgePredicateCall(predicate=left_predicate, params=left_params)
        rhs = ForgePredicateCall(predicate=right_predicate, params=right_params)
        constraint = ForgeConstraint(operator=ForgeOperator.OR, lhs=lhs, rhs=rhs)
        self._visitor_output_stack.append(constraint)

        return False
    




    """

    TOP LEVEL VISITORS

    """
    def visit_Assign(self, node: Assign):
        """
        Visits Assign nodes. Corresponds to variable assignment in Python.
        """

        # Retrieve the target
        targets = node.targets
        value = node.value

        node.value.visit(self)

        if value and isinstance(value, Call) and isinstance(value.func, Name) and value.func.value == "nondet":
            # It's a nondet assignment
            nondet_var_name = targets[0].target.value
            if not isinstance(nondet_var_name, str): 
                raise ValueError("Nondet variable name is not a string.")
            self.__cur_var = nondet_var_name # FIXME: Remove the assumption that a current variable is always set (via a nondet or regular assignment)

            # print("State of the stack:", self._visitor_output_stack)
            forge_predicate_call = self._visitor_output_stack.pop()
            # print("Expr received after visiting Call node: ", self._forge_constraint_to_str(forge_predicate_call))

            # Get the source field being assigned to the nondet variable
            nondet_source = forge_predicate_call.params[0]
            if not isinstance(nondet_source, ForgeAttributeAccess):
                raise ValueError("Nondet source expression is not an attribute access.")

            # Add nondet var to class metadata
            type_name = self.get_ds_class_field_type(nondet_source)
            self.types_to_vars[type_name].append(nondet_var_name)

            if nondet_var_name not in self.vars_to_constraints:
                self.vars_to_constraints[nondet_var_name] = []
        else:
            # NOTE: I don't think I need to modify this to use libCST visitor pattern, YET
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
            self.__associate_constraint_with_comment(constraint, node)
            self.vars_to_constraints[self.__cur_var].append(constraint)
        
        return False
    
    # def vist_Expr(self, node: Expr):
    #     """
    #     Visit an expression node. Currently only handles `assume` statements in Logic.py.
    #     """
    #     # Assume statements
    #     assume_call = node.value
    #     assume_arg = assume_call.args[0].value

    #     # Visit the assume arg
    #     assume_arg.visit(self)
    #     constraint = self._visitor_output_stack.pop()
    #     self.constraints.append(constraint)

    #     print("Expr received after visiting assume Call node: ", self._forge_constraint_to_str(constraint))
    #     self.__associate_constraint_with_comment(constraint, node)
    #     self.vars_to_constraints[self.__cur_var].append(constraint)

    #     # Error checking, just in case libCST doesn't catch when a visit function isn't defined
    #     if not isinstance(assume_arg, Call):
    #         raise ValueError("Assume argument is not a comparison.")
        
    #     return False

    def visit_Assert(self, node: Assert):
        """
        Visit an Assert node. Corresponds to `assert` statements in Logic.py.
        """
        assert_stmt = node.test
        assert_stmt.visit(self)
        constraint = self._visitor_output_stack.pop()
        self.constraints.append(constraint)
        self.__associate_constraint_with_comment(constraint, node)
        
        if self.__cur_var: # NOTE: is self.vars_to_constraints even necessary?
            self.vars_to_constraints[self.__cur_var].append(constraint)

        if not (assert_stmt and (isinstance(assert_stmt, Call) or isinstance(assert_stmt, BooleanOperation) or isinstance(assert_stmt, Comparison))):
            print("Unhandled branch within an assert statement:", dump(assert_stmt))
        
        return False



    """
    
    MODULE LEVEL VISITORS

    """
    def leave_Module(self, original_node):
        """
        Build the Forge code equivalent of the "validate" function with the generator's class variables.
        """
        lines = []
        lines.append("pred solution {")

        # Build existence variables
        quantifiers = []
        for type_name, nondets in self.types_to_vars.items():
            quantifiers.append(f"{', '.join(nondets)}: {type_name.capitalize()}")
        quantifierStr = ", ".join(quantifiers)
        
        lines.append(f"    some {quantifierStr} | {{")

        # Output constraints grouped by comment
        comment_blocks = []
        for (_, comment), constraints in self.comment_to_constraints.items():
            comment_block = []
            if comment != "":
                comment_block.append(f"        // {comment}")
            for constraint in constraints:
                comment_block.append(f"        {self._forge_constraint_to_str(constraint)}")
            if comment_block:
                comment_blocks.append("\n".join(comment_block))
        lines.append("\n\n".join(comment_blocks)) # add newline between comment blocks

        lines.append("    }")
        lines.append("}")
        self.forge_code = "\n".join(lines)

    def get_ds_field_type(self, field_name: str) -> str:
        return self.data_structure_metadata.get_field_type(field_name)
    
    def get_ds_class_field_type(self, expr: ForgeAttributeAccess) -> str:
        class_name = self._forge_constraint_to_str(expr.object)
        field_name = self._forge_constraint_to_str(expr.attr_name)

        return self.data_structure_metadata.get_class_field_type(class_name, field_name)
    


    """

    PARSING HELPERS

    """

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
                params_as_strs = [self._forge_constraint_to_str(p) for p in params]
                return f"{predicate}[{', '.join(params_as_strs)}]"
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
        function = self._expr_to_forge(node.value) # FIXME: change this to a `visit()` and delete `_expr_to_forge()`
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