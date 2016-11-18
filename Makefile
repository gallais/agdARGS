all:
	./build.sh agdARGS/Examples/Sum.agda
	./build.sh agdARGS/Examples/WordCount.agda
clean:
	rm -rf __build/
