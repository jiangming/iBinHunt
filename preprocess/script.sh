#!/bin/bash

dot -Tps cg1.dot > cg1.ps
dot -Tps cg2.dot > cg2.ps
gv cg1.ps &
gv cg2.ps &

