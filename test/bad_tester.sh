#!/bin/bash

goods=0
all=0

for i in lattests/bad/*.lat; do
    let "all=all+1"
    if $1 $i; then
        echo $(basename $i) " passed :("
    else
        echo $(basename $i) " OK! :)"
        let "good=good+1"
    fi;
done;

echo "$good / $all correct answers"