#!/usr/bin/env python

import os
import sys

from setuptools import setup

os.chdir(os.path.dirname(sys.argv[0]) or ".")

try:
    long_description = open("README.rst", "U").read()
except IOError:
    long_description = "See https://github.com/huyz/wayslack"

setup(
    name="wayslack2",
    version="0.4.4",
    url="https://github.com/huyz/wayslack",
    author="Huy Z",
    author_email="h-pypi-pub@huyz.us",
    description="The Wayslack Machine: incrementally archive Slack messages and files using Slack's team export format",
    long_description=long_description,
    long_description_content_type="text/x-rst",
    py_modules=["wayslack"],
    entry_points={
        'console_scripts': [
            'wayslack = wayslack:main',
        ],
    },
    install_requires=[
        "PyYAML<4",
        "pathlib<2",
        "slacker<1",
        "requests<3",
    ],
    license="BSD",
    classifiers=[ x.strip() for x in """
        Development Status :: 3 - Alpha
        Environment :: Console
        License :: OSI Approved :: BSD License
        Natural Language :: English
        Operating System :: OS Independent
        Programming Language :: Python :: 2
        Topic :: Utilities
    """.split("\n") if x.strip() ],
)
