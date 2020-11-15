#!/usr/bin/env zsh

autopep8 --aggressive --aggressive -i $(find src | grep "\.py$" | grep -v env)
