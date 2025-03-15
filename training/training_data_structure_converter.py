# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

from typing import Any, Optional

from libcst import (
    AnnAssign,
    Annotation,
    BaseAssignTargetExpression,
    BaseExpression,
    ClassDef,
    CSTVisitor,
    Name,
    Subscript,
)
from libcst.display import dump


# Name of the property describing the type of an entry inside a JSON schema.
_TYPE: str = "type"

# Name of the property in a JSON schema describing the properties of the
# associated JSON object.
_PROPERTIES: str = "properties"


class JsonSchemaObject:
    """
    Helper to create JSON schema type information for object types.
    """

    def __init__(self) -> None:
        self.json_schema: dict[str, Any] = {
            _TYPE: "object",
            _PROPERTIES: {},
        }

    def set_property(self, name: str, schema: dict[str, Any]) -> None:
        """
        Sets the type of a property inside this JSON schema object.
        """
        self.json_schema[_PROPERTIES][name] = schema


class JsonSchemaArray:
    """
    Helper to create JSON schema type information for array types.
    """

    @staticmethod
    def create(items_schema: Any) -> dict[str, Any]:
        return {_TYPE: "array", "items": items_schema}


class JsonSchemaPrimitive:
    """
    Helper to create JSON schema type information for primitive Python types.
    """

    @staticmethod
    def create(python_type_name: str) -> dict[str, Any]:
        json_type_name: str = python_type_name
        match (python_type_name):
            case "float":
                json_type_name = "number"
            case "int":
                json_type_name = "integer"
            case "range":
                json_type_name = "integer"
            case "str":
                json_type_name = "string"
        return {_TYPE: json_type_name}


class AnnotationToJsonSchemaConverter(CSTVisitor):
    """
    Helper to extract type information from attributes (i.e. annotated
    assignments) inside a class.
    """

    def __init__(self, class_schemas: dict[str, JsonSchemaObject]) -> None:
        self.type: dict[str, Any] = {}
        self.__class_schemas: dict[str, JsonSchemaObject] = class_schemas

    def leave_Subscript(self, original_node: Subscript) -> None:
        value: BaseExpression = original_node.value
        if isinstance(value, Name):
            if value.value == "list":
                self.type = JsonSchemaArray.create(self.type)

    def visit_Name(self, node: Name) -> Optional[bool]:
        name: str = node.value
        class_schema: Optional[JsonSchemaObject] = self.__class_schemas.get(name)
        self.type = (
            class_schema.json_schema
            if class_schema
            else JsonSchemaPrimitive.create(node.value)
        )

    @staticmethod
    def get_type(
        annotation: Annotation, class_schemas: dict[str, JsonSchemaObject]
    ) -> dict[str, Any]:
        """
        Provides the JSON schema type to use for the given type annotation of a
        class attribute.

        Args:
            annotation (Annotation): Type annotation of a Python class attribute
            (i.e. an annotated assignment).
            class_schemas (dict[str, JsonSchemaObject]): All known classes as
            JSON schema object types, so that we can inline class names to their
            actual JSON schema object type.
        """
        visitor = AnnotationToJsonSchemaConverter(class_schemas)
        annotation.visit(visitor)
        return visitor.type


class PythonDataStructureToJsonSchemaConverter(CSTVisitor):
    """
    Helper class to convert a series of Python class data structures into a
    JSON schema. This used when performing RL training, where the RL scorer VCs
    are based originally on a Python data structure. In these cases, we want
    the model to generate JSON objects that match this original Python data
    structure. The resulting JSON schema will then be passed to the model as
    part of the system prompt, so that it generates solutions in JSOn format
    that are compatible with the VCs.
    """

    def __init__(self) -> None:
        super().__init__()
        self.json_schema: dict[str, Any] = {}
        self.__class_schemas: dict[str, JsonSchemaObject] = {}
        self.__current_class_schema = JsonSchemaObject()

    def leave_ClassDef(self, original_node: ClassDef) -> None:
        self.json_schema = self.__current_class_schema.json_schema
        self.__current_class_schema = JsonSchemaObject()

    def visit_AnnAssign(self, node: AnnAssign) -> Optional[bool]:
        target: BaseAssignTargetExpression = node.target
        if not isinstance(target, Name):
            raise ValueError(
                f"Expected annotated assignments only as attribute declarations: {dump(node)}"
            )

        attribute_name: str = target.value
        type_schema: dict[str, Any] = AnnotationToJsonSchemaConverter.get_type(
            node.annotation, self.__class_schemas
        )
        self.__current_class_schema.set_property(attribute_name, type_schema)
        return False

    def visit_ClassDef(self, node: ClassDef) -> Optional[bool]:
        self.__class_schemas[node.name.value] = self.__current_class_schema
