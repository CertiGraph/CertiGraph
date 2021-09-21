CLIGHTGEN=/home/leowwx/Desktop/CompCert-3.7/clightgen
for cfile in *.c; do
    echo $cfile
    $CLIGHTGEN -DCOMPCERT -normalize -isystem .. $cfile
done