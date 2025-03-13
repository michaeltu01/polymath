# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

from output.dummy_sample_output_converter import DummySampleOutputConverter
from output.sample_output_converter import SampleOutputConverter
from plugin.plugin_loader import PluginLoader


def create_sample_output_converter() -> SampleOutputConverter:
    """
    Default factory for sample output conversionAPI. Modifying this method
    allows to activate a custom sample output format when generating training
    data across benchmarks and end-to-end tests.

    Additionally, a sample output converter implementation from an external module can
    be configured dynamically using the environment variables
    `SAMPLE_OUTPUT_CONVERTER_MODULE_PATH` and `SAMPLE_OUTPUT_CONVERTER_COMPLETION_CLASS_NAME`. They must
    provide the same constructor as DummySampleOutputConverter and implement the
    SampleOutputConverter interface.

    Returns: Sample output converter to use for training data generation.
    """
    plugin: PluginLoader[SampleOutputConverter] = PluginLoader(
        "sample_output_converter"
    )
    if plugin.is_configured:
        return plugin.factory()

    return DummySampleOutputConverter()
