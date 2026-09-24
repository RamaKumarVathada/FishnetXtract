#!/usr/bin/env python3
# -*- coding: utf-8 -*-

def classFactory(iface):
    """
    Loads the FishnetXtract class from your main python file.
    This function is called natively by QGIS when initializing the plugin.
    """
    from .FishnetXtract import FishnetXtract
    return FishnetXtract(iface)