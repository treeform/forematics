# Forematics is a Metamath verifier written in Nim

Big thanks goes to David A. Wheeler and his python version: https://github.com/david-a-wheeler/mmverify.py

## Usage
```
nim c -d:release --gc:arc -r src/forematics.nim "mm/set.mm"
```

Download the letest set.mm from https://github.com/metamath/set.mm
