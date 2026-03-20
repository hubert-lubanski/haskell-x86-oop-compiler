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

if [ -z "$2" ]; then
    echo "Proszę podać folder docelowy z plikami .lat i .output"
    exit 1
fi

for i in ${2}*.lat; do
    let "all=all+1"
    if time $1 $i &>.latte.dump; then
        eval "./${i%.lat} > ${i%.lat}.result"
        if diff "${i%.lat}.output" "${i%.lat}.result"; then
            echo $(basename $i) " PASSED :)"
            let "good=good+1"
        else
            cat .latte.dump;
            echo -e "\n$Red" $(basename $i) " FAILED ON RUNTIME :( $Color_Off\n"
            exit 1
        fi
        rm .latte.dump
        #rm "lattests/good/${i%.lat}"
    else
        cat .latte.dump;
        echo -e "\n$Red" $(basename $i) " FAILED :( $Color_Off\n"
        exit 1
    fi;
done;

echo "$good / $all correct answers"