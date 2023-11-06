#! /bin/bash


output="out"

python_file="src/main.py"

while getopts ":o:" opt; do
    case "${opt}" in
    o)
        output="$OPTARG"
        ;;
    *)
        break;
        ;;
    esac
done

echo $output
if [ ! -d log/ ]; then
    mkdir log/
fi


python3 $python_file $@ 

if [ $? == 0 ]; then
    java -jar /opt/plantuml.jar -tpng $output
   if [ -d \?/ ]; then
       rm -rdf \?/
   fi
fi

