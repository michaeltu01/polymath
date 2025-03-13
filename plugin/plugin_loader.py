from importlib.abc import Loader
from importlib.machinery import ModuleSpec
from importlib.util import module_from_spec, spec_from_file_location
from os import getenv
from types import ModuleType
from typing import Optional, Type, TypeVar


# Interface that the class provided by the plug-in should implement.
PluginInterface = TypeVar("PluginInterface")


class PluginLoader[PluginInterface]:
    """
    Helper to load external classes impolementing an expected interface.
    """

    def __init__(self, plugin_name: str) -> None:
        """
        Args:
            plugin_name (str): Name of the plug-in to load. The environment
            variables defining the module path and the class name to load are
            derived from an upeprcase version of this name.
        """
        env_var_prefix: str = plugin_name.upper()
        self.__class_name: str = getenv(f"{env_var_prefix}_CLASS_NAME", "")
        self.__module_path: str = getenv(f"{env_var_prefix}_MODULE_PATH", "")
        self.__module_name: str = f"dynamic_{plugin_name}"

    @property
    def is_configured(self) -> bool:
        """
        Indicates whether the necessary environment variables to load the
        plug-in were set.
        """
        return bool(self.__module_path) and bool(self.__class_name)

    @property
    def factory(self) -> Type[PluginInterface]:
        """
        If `is_configured` is set, this property provides the configured type.
        This can be used to instantiate an object of the plug-in type.
        """
        spec: Optional[ModuleSpec] = spec_from_file_location(
            self.__module_name, self.__module_path
        )
        if not spec:
            raise ValueError(
                f"Could not read Python module from file: {self.__module_path}"
            )

        plugin_module: ModuleType = module_from_spec(spec)
        loader: Optional[Loader] = spec.loader
        if loader:
            loader.exec_module(plugin_module)
        return getattr(plugin_module, self.__class_name)
