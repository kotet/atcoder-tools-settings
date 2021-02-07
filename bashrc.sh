atcinit() {
  atcoder-tools gen --lang d --template ~/.atcoder-tools/template.d $1
  cd ~/atcoder-workspace/$1
  ln -s ~/.atcoder-tools/snippets.d snippets.d
}

atctest() {
  pushd $1
  local BUILD="docker run --rm -v $PWD:/src -w /src dlang2/dmd-ubuntu:2.091.0 dmd -wi -m64 -O -release -inline -boundscheck=off main.d"
  local DEBUG="docker run --rm -v $PWD:/src -w /src dlang2/dmd-ubuntu:2.091.0 dmd -g -debug main.d"

  if [ "$2" = "debug" ]; then
    echo $DEBUG
    $DEBUG
  else
    echo $BUILD
    $BUILD
  fi

  if [ ! $? = 0 ]; then
    echo "Build failed."
    return
  fi

  atcoder-tools test
  popd
}

atcsubmit() {
  pushd $1
  
  local BUILD="docker run --rm -v $PWD:/src -w /src dlang2/dmd-ubuntu:2.091.0 dmd -wi -m64 -O -release -inline -boundscheck=off main.d"

  echo $BUILD
  $BUILD

  if [ ! $? = 0 ]; then
    echo "Build failed."
    return
  fi

  atcoder-tools submit -u
  popd
}
