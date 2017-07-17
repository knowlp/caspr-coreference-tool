#!/bin/bash

# this script runs crasp on all examples

FAIL=0

AUTOIN="auto/inputs/"
AUTOOUT="auto/outputs/"
for obj in v va u ua; do
  echo -n "objective $obj --all"
  ../caspr --obj=$obj --all --out=out.$obj.conll \
    --ann=$AUTOIN/in1.conll --ann=$AUTOIN/in2.conll --ann=$AUTOIN/in3.conll --ann=$AUTOIN/in4.conll
  if diff out.$obj.conll $AUTOOUT/out.$obj.conll; then
    echo "OK"
  else
    echo "FAIL"
    ((FAIL++))
    echo "see diff above"
  fi
done

#obj=u
#f=redo1
#cp $f.in.conll $f.$obj.conll
#./crasp --obj=$obj --all --redo=$f.$obj.conll \
#  --ann=in1.conll --ann=in2.conll --ann=in3.conll --ann=in4.conll 
#cat $f.$obj.conll

if test $FAIL -eq 0; then
  echo "all tests succeeded!"
  exit 0;
else
  echo "some tests failed! ($FAIL)"
  exit 1;
fi

