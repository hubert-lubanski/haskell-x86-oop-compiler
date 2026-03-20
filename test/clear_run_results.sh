#!/bin/bash

# Reset
Color_Off='\033[0m'       # Text Reset

# Regular Colors
Black='\033[0;30m'        # Black
Red='\033[0;31m'          # Red
Green='\033[0;32m'        # Green
Yellow='\033[0;33m'       # Yellow
Blue='\033[0;34m'         # Blue
Purple='\033[0;35m'       # Purple
Cyan='\033[0;36m'         # Cyan
White='\033[0;37m'        # White

all=0

if [ -z "$1" ]; then
    echo "Proszę podać folder do wyczyszczenia"
    exit 1
fi

for i in ${1}*.lat; do
    echo "removing ${i%.lat} ${i%.lat}.s ${i%.lat}.result"
    rm -f "${i%.lat}"
    rm -f "${i%.lat}.s"
    rm -f "${i%.lat}.result"
    rm -f .latte.dump
    let "all=all+1"
done;

echo "Test results removed ($all)"
