#!/usr/bin/env zsh

for input in $(ls failedtests/test_1*.sms)
do
    reps=1

    for i in {1..$reps};
    do
        tmpfile=.$(basename $input).out.tmp
        >&2 echo -ne "$input\t\t"
        ./proj2 < $input > $tmpfile
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

        #rm $tmpfile
    done
done
