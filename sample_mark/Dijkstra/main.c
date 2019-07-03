//
//  main.c
//  Dijkstra
//
//  Created by Anshuman Mohan on 14/6/19.
//  Copyright © 2019 Anshuman Mohan. All rights reserved.
//

#include "dijkstra.h"

int main(int argc, const char * argv[])
{
    setup();
    print_graph();
    dijkstra();
    getPaths();
    return 0;
}
