
for i in {1..100} 
    do
        python3 ./queens.py $i >queens.in
        ./base $i >check.in
        minisat queens.in queens.out >/dev/null
        minisat check.in check.out >/dev/null
        diff -s queens.out check.out
    done