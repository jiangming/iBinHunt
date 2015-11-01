CC = gcc
CFLAGS := -Wall

all: tograph

tograph: tograph.o
	$(CC) $(CFLAGS) -o $@ $^


	
clean:
	rm -f *.o tograph
	rm -rf debug
	rm -rf result