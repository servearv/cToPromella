#include <stdlib.h>
struct node {
    struct node *next;
    int value;
};

void test() {
    struct node *p = malloc(sizeof(struct node));
    p->value = 99;
    free(p);
}
