# Forematics is a Metamath verifier written in Nim

Metamath is project that atempts to build describe mathamtics from ground up starting from very simple axioms, building more and more complex theorems on top. While having everything machine checked using a very simple verfier. Forematics is a metamath verifyer written in Nim.

Big thanks to the https://github.com/david-a-wheeler/mmverify.py project which was used a base and insperation.

## Usage
```
nim c -d:release --gc:arc -r src/forematics.nim "mm/set.mm"
```

Download the letest set.mm from https://github.com/metamath/set.mm
