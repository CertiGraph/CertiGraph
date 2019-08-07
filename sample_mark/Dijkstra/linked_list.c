#include "linked_list.h"
#include <stdlib.h>
#include <limits.h>
#include <stdio.h>
#define IFTY INT_MAX

/* ****************************** */
/* Linked List Masquerading as PQ */
/* ****************************** */

struct Node { int vertex; int weight; struct Node *next; struct Node *prev;};

void push (int vertex, int weight, struct Node **list) {
    struct Node* newHead = (struct Node *) malloc (sizeof (struct Node));
    newHead->vertex = vertex;
    newHead->weight = weight;
    newHead->prev=NULL;
    newHead->next = *list;
    if (*list != NULL)
        (*list)->prev = newHead;
    *list = newHead;
}

void deleteNode (struct Node *del, struct Node **head) {
    if (*head == NULL || del == NULL) return;
    if (*head == del) *head = del->next;
    if (del->next != NULL) del->next->prev = del->prev;
    if (del->prev != NULL) del->prev->next = del->next;
    free(del);
    return;
}

int popMin (struct Node **head) {
    int minWeight = IFTY;
    int minVertex = -1;
    struct Node *minNode = NULL;
    struct Node *current = *head;
    while (current != NULL) {
        if (current->weight < minWeight) {
            minWeight = current->weight;
            minVertex = current->vertex;
            minNode = current;
        } current = current->next;
    }
    deleteNode(minNode, head);
    return minVertex;
}

void adjustWeight (int vertex, int newWeight, struct Node **head) {
    struct Node *current = *head;
    while (current != NULL) {
        if (current->vertex == vertex) {
            current->weight = newWeight;
            return;
        } current = current->next;
    }
}

void print_verts (struct Node *list) {
    if (list == NULL) printf("A blank list was provided.\n");
    struct Node *current = list;
    while (current != NULL) {
        printf ("%d\t", current->vertex);
        current = current->next;
    } printf ("\n");
}

// Used only for testing, will be removed eventually.
void print_list (struct Node *list) {
    if (list == NULL) printf("A blank list was provided.\n");
    struct Node *current = list;
    while (current != NULL) {
        printf ("(%d, %d)\t", current->vertex, current->weight);
        current = current->next;
    } printf ("\n");
}
