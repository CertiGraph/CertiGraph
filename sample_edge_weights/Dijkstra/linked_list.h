//
//  linked_list.h
//  Dijkstra
//
//  Created by Anshuman Mohan on 14/6/19.
//  Copyright © 2019 Anshuman Mohan. All rights reserved.
//

#ifndef linked_list_h
#define linked_list_h
#endif /* linked_list_h */

struct Node;
void push (int vertex, int weight, struct Node **head);
void print_list (struct Node *head);
int popMin (struct Node **head);
void adjustWeight (int vertex, int newWeight, struct Node **head);
void print_verts (struct Node *list);
void print_list (struct Node *list);
