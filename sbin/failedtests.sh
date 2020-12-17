#!/usr/bin/env zsh

for input in  "failedtests/test_40_120_23_7_3_120_129.sms" "failedtests/test_75_150_17_7_2_150_774.sms" "failedtests/test_100_200_11_5_3_200_186.sms" "failedtests/test_100_300_17_5_3_300_471.sms" "failedtests/test_100_200_11_7_2_200_192.sms" "failedtests/test_100_300_23_5_3_300_548.sms" "failedtests/test_100_200_23_7_2_200_323.sms"
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
