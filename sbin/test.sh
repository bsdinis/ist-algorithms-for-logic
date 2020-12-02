#!/usr/bin/env zsh

for input in $(ls tests/*.sms)
do
    reps=1
    echo $input | grep "2" >/dev/null
    if [ $? -eq 0 ]
    then
        reps=1
    fi
    echo $input | grep "3" >/dev/null
    if [ $? -eq 0 ]
    then
        reps=1
    fi
    echo $input | grep "4" >/dev/null
    if [ $? -eq 0 ]
    then
        reps=1
    fi
    echo $input | grep "5" >/dev/null
    if [ $? -eq 0 ]
    then
        reps=1
    fi

    for i in {1..$reps};
    do
        tmpfile=.$(basename $input).out.tmp
        >&2 echo -ne "$input\t\t"
        runsolver -w $tmpfile.loud --input=$input -o $tmpfile ./proj3
        elapsed=$(grep 'Current children cumulated CPU time (s)' $tmpfile.loud | tail -n 1 | cut -d')' -f 2)
        echo "$elapsed s"
        ./checker/checker $input $tmpfile | grep 'OK!' > /dev/null
        if [ $? -ne 0 ]
        then
            echo "Failed on test $input"
            exit -1
        fi

        diff -q <(head -n 1 $tmpfile) <(head -n 1 ${input%.sms}.out) >/dev/null
        if [ $? -ne 0 ]
        then
            echo "Failed on test $input: failed to maximize"
            exit -1
        fi

        rm $tmpfile
        rm $tmpfile.loud
    done
done
