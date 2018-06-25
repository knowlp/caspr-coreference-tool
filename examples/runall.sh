#!/bin/bash

# this script runs crasp on all examples

AT=1
FAIL=0

WORKDIR=tmp
rm -r $WORKDIR
mkdir -p $WORKDIR

AUTOIN="auto/inputs/"
AUTOOUT="auto/outputs/"
for obj in v va u ua; do
  echo "TEST RUN $AT: AUTO objective $obj --all"
  ((AT++))
  # run
  ../caspr --canonicalize --obj=$obj --all --out=$WORKDIR/out.$obj.conll \
    --ann=$AUTOIN/in1.conll --ann=$AUTOIN/in2.conll --ann=$AUTOIN/in3.conll --ann=$AUTOIN/in4.conll
  # compare
  if diff $WORKDIR/out.$obj.conll $AUTOOUT/out.$obj.conll; then
    echo "TEST OK"
  else
    echo "TEST FAIL"
    ((FAIL++))
    echo "see diff above"
  fi
done

obj=u
SEMIAUTOIN="semiauto/inputs/"
SEMIAUTOOUT="semiauto/outputs/"
for f in redo1 redo2; do
  echo "TEST RUN $AT: SEMIAUTO file $f objective $obj --all"
  ((AT++))
  cp $SEMIAUTOIN/$f.in.conll $WORKDIR/$f.inout.$obj.conll
  # run
  ../caspr --canonicalize --obj=$obj --all --redo=$WORKDIR/$f.inout.$obj.conll \
    --ann=$AUTOIN/in1.conll --ann=$AUTOIN/in2.conll --ann=$AUTOIN/in3.conll --ann=$AUTOIN/in4.conll 
  # compare
  diff $WORKDIR/$f.inout.$obj.conll $SEMIAUTOOUT/$f.inout.$obj.canonical.conll
  OUTOK=$?
  diff $WORKDIR/$f.inout.$obj.conll.clean $SEMIAUTOOUT/$f.inout.$obj.canonical.conll.clean
  CLEANOK=$?
  if test "$OUTOK$CLEANOK" = "00"; then
    echo "TEST OK"
  else
    echo "TEST FAIL"
    echo "$OUTOK$CLEANOK"
    ((FAIL++))
    echo "see diff above"
  fi
done

if test $FAIL -eq 0; then
  echo "all tests succeeded!"
  exit 0;
else
  echo "some tests failed! ($FAIL)"
  exit 1;
fi

