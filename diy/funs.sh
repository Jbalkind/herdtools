erasetxt ()
{
  for t in *.txt
  do
    case $t in
     LICENSE.txt|CHANGES.txt|README.txt|INSTALL.txt|VERSION.txt)
     ;;
    
     *)
       /bin/rm -f $t
       ;;
    esac
 done
}

erasesrc ()
{
  if [ !  -e _build/$1  ]
  then
     echo "Erasing $1"
    /bin/rm $1
  fi
}

TMPFILE=/tmp/tmp.$$

cleandir ()
{
  d=$1
  cp $DIR/LICENSE.txt $d && \
  cd $d && \
  sed -e 's|PREFIX=$$HOME|PREFIX=/usr/local|' -e 's|EXTRAPROGS=.*|EXTRAPROGS=|' Makefile > /tmp/tmp.$$ && mv $TMPFILE Makefile && \
  make && \
  erasetxt && \
  if [ -d lib ]
  then
    for f in lib/*.ml lib/*.ml[iyl]
    do
      erasesrc $f
    done
  fi && \
  for f in *.ml *.ml[iyl]
  do
    erasesrc $f
  done && make clean
}