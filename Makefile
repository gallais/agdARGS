all:
	./build.sh agdARGS/Examples/Sum.agda
	./build.sh agdARGS/Examples/WordCount.agda
	./build.sh agdARGS/Examples/Echo.agda

clean:
	rm -rf __build/
