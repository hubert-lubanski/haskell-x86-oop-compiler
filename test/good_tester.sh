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

goods=0
all=0

for i in lattests/good/*.lat; do
    let "all=all+1"
    if $1 $i; then
        echo $(basename $i) " PASSED :)"
        let "good=good+1"
    else
        echo -e "\n$Red" $(basename $i) " FAILED :( $Color_Off\n"
    fi;
done;

echo "$good / $all correct answers"