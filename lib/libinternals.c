#include "libinternals.h"

void internal(printInt)(int64_t x){
    printf("%ld\n", x);
}

void internal(printString)(char *s){
    printf("%s\n", s);
}

int64_t internal(readInt)(void){
    int64_t _;
    scanf("%ld%*[^\n]\n", &_); 
    return _;
}

char * internal(readString)(void){
    char *str;
    scanf("%ms", &str); // Auto alokacja dzięki POSIX
    return str;
}

char * internal(strcat)(char * s1, char * s2){
    uint64_t sl1 = strlen(s1);
    uint64_t sl2 = strlen(s2);
    void * memory = malloc(sl1 + sl2 + 1);
    memcpy(memory, s1, sl1);
    memcpy(memory + sl1, s2, sl2 + 1);
    return memory;
}

__attribute__((noreturn))
void internal(makeError)(void){
    printf("runtime error\n");
    exit(1);
}

void *internal(heap_alloc)(int64_t size){

    if (size < 0) {
        printf("Fatal: wrong allocation size of %ld bytes\n", size);
        exit(1);
    }

    void * memory = malloc(size + 8);

    if (memory == NULL) {
        printf("Fatal: insufficient memory\n");
        exit(1);
    }

    return (memory + 8);
}