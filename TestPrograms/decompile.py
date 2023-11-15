import os
import sys

if __name__ == "__main__":
    path = sys.argv[1]
    files = os.listdir(path)
    for file in files:
        if file.endswith(".class"):
            file_path = path+"\\"+file
            os.system(f"docker run --rm -i kalhauge/jvm2json:latest jvm2json <{file_path} >{file_path.split('.')[-2]+'.json'}")
