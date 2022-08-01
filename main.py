#  COP 3530 Summer 2022
#  Project 3
#  Group 1
#  Members: Aaron Hamburger, Sergio Arcila, Zachary Schirm
#  Present...
#  The Magical Maze Solver!


import pygame
import time
import random
import networkx as nx
import math
import pygame_menu
import heapq
import array as arr
from typing import Tuple, Any
import sys

"""
This is the Maze class!
The Maze class has private member variables that are accessible only via getters.
The Maze class is responsible for all aspects of maze creation, visualization, and pathfinding/solving.
The class has custom implementations of Dijkstra's algorithm, as well as Breadth First and
Depth First searches.
The class is capable of reporting time to solve all algorithms, solution paths via ascending order
vectors, and number of nodes searched by each algorithm to find a solution.
"""


class Maze:

    def __init__(self, the_screen, maze_font, scale_factor, solve_speed, create_speed):
        self._local_execution_time_dijkstra = 0
        self._local_execution_time_dfs = 0
        self._local_execution_time_bfs = 0
        self._local_maze_solution_dijkstra = []
        self._local_maze_solution_bfs = []
        self._local_maze_solution_dfs = []
        self._solved = False
        self._high_nodes = False
        self._high_nodes_menu_choice = 1
        self._the_screen = the_screen
        self._font = maze_font
        self._local_winning_algo = 'Dijkstra'
        self._dijkstra_nodes_visited = 1
        self._dfs_nodes_visited = 1
        self._bfs_nodes_visited = 1
        self._rows = 0
        self._global_node_count = 49
        self._visited_cells = []
        self._creation_stack = []
        self._local_maze_graph = nx.Graph()
        self._GRAPH_SCALE_FACTOR = scale_factor
        self._solve_speed = solve_speed
        self._create_speed = create_speed

    # based on user selected maze size, determines number of rows in the maze
    def define_rows(self):
        self._rows = math.sqrt(
            self._global_node_count)  # the global node count needs to be perfect square to make cubic maze
        self._rows = int(self._rows)  # wants to give float value - need int - casting to same

    # method to construct maze grid of squares
    def build_maze(self, node_count):

        # add node_number (user input) of nodes to mazeGraph graph (networkx)
        for i in range(1, node_count + 1):
            self._local_maze_graph.add_node(i)

        # draw background color of maze
        pygame.draw.rect(self._the_screen, BLUE, pygame.Rect(GRAPH_X_OFFSET + 20, GRAPH_Y_OFFSET + 20,
                                                             GRAPH_SCALE_FACTOR * 20 * self._rows,
                                                             GRAPH_SCALE_FACTOR * 20 * self._rows))

        # draw all individual cells (Rects), walls will overlap but will be drawn over during maze creation
        for j in range(0, self._rows):
            for k in range(0, self._rows):
                pygame.draw.rect(self._the_screen, WHITE,
                                 pygame.Rect((20 + GRAPH_X_OFFSET + j * 20 * GRAPH_SCALE_FACTOR)
                                             , (20 + GRAPH_Y_OFFSET + k * 20 * GRAPH_SCALE_FACTOR),
                                             20 * GRAPH_SCALE_FACTOR, 20 * GRAPH_SCALE_FACTOR), width=1)

        # refresh display with above
        pygame.display.update()

    # The following methods are used to 'clear' the maze visually as it is constructed and edges
    # are added between nodes per the algorithm we are using.  The walls are not actually being deleted but
    # rather new rectangles are being drawn over the maze to 'clear' the walls (much easier, looks fine)

    # clear wall upward
    def move_up(self, node_number):
        if node_number % self._rows == 0:
            x_pos = self._rows
            y_pos = int(node_number / (self._rows + 1))
        else:
            x_pos = int(node_number % self._rows)
            y_pos = int(node_number / self._rows)
        pygame.draw.rect(self._the_screen, BLUE, pygame.Rect(x_pos * 20 * GRAPH_SCALE_FACTOR + 1 + GRAPH_X_OFFSET,
                                                             y_pos * 20 * GRAPH_SCALE_FACTOR + 1 + GRAPH_Y_OFFSET,
                                                             18 * GRAPH_SCALE_FACTOR, 38 * GRAPH_SCALE_FACTOR))
        pygame.display.update()

    # clear wall rightward
    def move_right(self, node_number):
        if node_number % self._rows == 0:
            x_pos = self._rows
            y_pos = int(node_number / (self._rows + 1))
        else:
            x_pos = int(node_number % self._rows)
            y_pos = int(node_number / self._rows)
        pygame.draw.rect(self._the_screen, BLUE, pygame.Rect(x_pos * 20 * GRAPH_SCALE_FACTOR + 1 + GRAPH_X_OFFSET,
                                                             y_pos * 20 * GRAPH_SCALE_FACTOR + 21 + GRAPH_Y_OFFSET,
                                                             38 * GRAPH_SCALE_FACTOR, 18 * GRAPH_SCALE_FACTOR))
        pygame.display.update()

    # clear wall leftward
    def move_left(self, node_number):
        if node_number % self._rows == 0:
            x_pos = self._rows
            y_pos = int(node_number / (self._rows + 1))
        else:
            x_pos = int(node_number % self._rows)
            y_pos = int(node_number / self._rows)
        pygame.draw.rect(self._the_screen, BLUE, pygame.Rect(x_pos * 20 * GRAPH_SCALE_FACTOR - 19 + GRAPH_X_OFFSET,
                                                             y_pos * 20 * GRAPH_SCALE_FACTOR + 21 + GRAPH_Y_OFFSET *
                                                             GRAPH_SCALE_FACTOR, 38 * GRAPH_SCALE_FACTOR, 18 *
                                                             GRAPH_SCALE_FACTOR))
        pygame.display.update()

    # clear wall downward
    def move_down(self, node_number):
        if node_number % self._rows == 0:
            x_pos = self._rows
            y_pos = int(node_number / (self._rows + 1))
        else:
            x_pos = int(node_number % self._rows)
            y_pos = int(node_number / self._rows)
        pygame.draw.rect(self._the_screen, BLUE, pygame.Rect(x_pos * 20 * GRAPH_SCALE_FACTOR + 1 + GRAPH_X_OFFSET,
                                                             y_pos * 20 * GRAPH_SCALE_FACTOR + 21 + GRAPH_Y_OFFSET,
                                                             18 * GRAPH_SCALE_FACTOR, 38 * GRAPH_SCALE_FACTOR))
        pygame.display.update()

    # color individual cell (for showing maze construction/tracking)
    def color_one_cell(self, node_number):
        if node_number % self._rows == 0:
            x_pos = self._rows
            y_pos = int(node_number / (self._rows + 1))
        else:
            x_pos = int(node_number % self._rows)
            y_pos = int(node_number / self._rows)
        pygame.draw.rect(self._the_screen, YELLOW, pygame.Rect(x_pos * 20 * GRAPH_SCALE_FACTOR + 1 + GRAPH_X_OFFSET,
                                                               y_pos * 20 * GRAPH_SCALE_FACTOR + 21 + GRAPH_Y_OFFSET,
                                                               18 * GRAPH_SCALE_FACTOR, 18 * GRAPH_SCALE_FACTOR))
        pygame.display.update()

    # will color beginning cell of maze GREEN
    def color_beginning(self, node_number):
        if node_number % self._rows == 0:
            x_pos = self._rows
            y_pos = int(node_number / (self._rows + 1))
        else:
            x_pos = int(node_number % self._rows)
            y_pos = int(node_number / self._rows)
        pygame.draw.rect(self._the_screen, GREEN, pygame.Rect(x_pos * 20 * GRAPH_SCALE_FACTOR + 1 + GRAPH_X_OFFSET,
                                                              y_pos * 20 * GRAPH_SCALE_FACTOR + 21 + GRAPH_Y_OFFSET,
                                                              18 * GRAPH_SCALE_FACTOR, 18 * GRAPH_SCALE_FACTOR))
        pygame.display.update()

    # will color end cell of maze RED
    def color_end(self, node_number):
        if node_number % self._rows == 0:
            x_pos = self._rows
            y_pos = int(node_number / (self._rows + 1))
        else:
            x_pos = int(node_number % self._rows)
            y_pos = int(node_number / self._rows)
        pygame.draw.rect(self._the_screen, RED, pygame.Rect(x_pos * 20 * GRAPH_SCALE_FACTOR + 1 + GRAPH_X_OFFSET,
                                                            y_pos * 20 * GRAPH_SCALE_FACTOR + 21 + GRAPH_Y_OFFSET,
                                                            18 * GRAPH_SCALE_FACTOR, 18 * GRAPH_SCALE_FACTOR))
        pygame.display.update()

    # return highlighted cell to original color
    # this is used when showing that the maze generating algorithms is 'backtracking'
    # to find the next node in stack with unvisited nodes
    def uncolor_one_cell(self, node_number):
        if node_number % self._rows == 0:
            x_pos = self._rows
            y_pos = int(node_number / (self._rows + 1))
        else:
            x_pos = int(node_number % self._rows)
            y_pos = int(node_number / self._rows)
        pygame.draw.rect(self._the_screen, BLUE, pygame.Rect(x_pos * 20 * GRAPH_SCALE_FACTOR + 1 + GRAPH_X_OFFSET,
                                                             y_pos * 20 * GRAPH_SCALE_FACTOR + 21 + GRAPH_Y_OFFSET,
                                                             18 * GRAPH_SCALE_FACTOR, 18 * GRAPH_SCALE_FACTOR))
        pygame.display.update()

    # solution cell that shows small box in center to mark path/solution
    def show_solution_cell(self, node_number):
        if node_number % self._rows == 0:
            x_pos = self._rows
            y_pos = int(node_number / (self._rows + 1))
        else:
            x_pos = int(node_number % self._rows)
            y_pos = int(node_number / self._rows)
        pygame.draw.rect(self._the_screen, WHITE, pygame.Rect(x_pos * 20 * GRAPH_SCALE_FACTOR + 8 + GRAPH_X_OFFSET,
                                                              y_pos * 20 * GRAPH_SCALE_FACTOR + 28 + GRAPH_Y_OFFSET,
                                                              3 * GRAPH_SCALE_FACTOR, 3 * GRAPH_SCALE_FACTOR))
        pygame.display.update()

    # method to show the solution to the maze visually
    def display_maze_solution(self, maze_solution):
        for i in maze_solution:
            self.show_solution_cell(i)
            pygame.mixer.Sound.play(solve_click)
            time.sleep(self._solve_speed)

    # this is the recursive back-racker algorithm to generate the maze randomly
    # basically, it takes a node and determines how many UNVISITED neighbors in the maze it has that can be
    # travelled to.  It will randomly select one of those, break down the wall between it, then add an edge in the graph
    # between those nodes.  A stack is created of all previously visited nodes in case a dead end is reached,
    # in which case the loop will pop nodes off the stack until a node with unvisited neighbors is found and
    # then continue construction of the maze.
    def create_the_maze(self):
        self._visited_cells = []
        self._creation_stack = []
        self._creation_stack.append(1)  # starting cell goes into stack
        self._visited_cells.append(1)
        current_cell = 1
        while len(self._creation_stack) > 0:
            time.sleep(self._create_speed)
            cell_list = []
            if current_cell % self._rows != 0 and (current_cell + 1) not in self._visited_cells:
                cell_list.append("right")
            if (current_cell - 1) % self._rows != 0 and (current_cell - 1) not in self._visited_cells:
                cell_list.append("left")
            if (current_cell + self._rows) <= self._global_node_count and (
                    current_cell + self._rows) not in self._visited_cells:
                cell_list.append("down")
            if (current_cell - self._rows) > 0 and (current_cell - self._rows) not in self._visited_cells:
                cell_list.append("up")

            if len(cell_list) > 0:
                random_cell = random.choice(cell_list)
                if random_cell == "right":
                    self.move_right(current_cell)
                    self._local_maze_graph.add_edge(current_cell, current_cell + 1)
                    current_cell = current_cell + 1
                    self.color_one_cell(current_cell)  # visual to show creation
                    time.sleep(CREATE_SPEED)  # pause for effect
                    self.uncolor_one_cell(current_cell)  # erase creation visual
                    self._visited_cells.append(current_cell)
                    self._creation_stack.append(current_cell)

                elif random_cell == "left":
                    self.move_left(current_cell)
                    self._local_maze_graph.add_edge(current_cell, current_cell - 1)
                    current_cell = current_cell - 1
                    self.color_one_cell(current_cell)  # visual to show creation
                    time.sleep(CREATE_SPEED)  # pause for effect
                    self.uncolor_one_cell(current_cell)  # erase creation visual
                    self._visited_cells.append(current_cell)
                    self._creation_stack.append(current_cell)

                elif random_cell == "up":
                    self.move_up(current_cell)
                    self._local_maze_graph.add_edge(current_cell, current_cell - self._rows)
                    current_cell = current_cell - self._rows
                    self.color_one_cell(current_cell)  # visual to show creation
                    time.sleep(CREATE_SPEED)  # pause for effect
                    self.uncolor_one_cell(current_cell)  # erase creation visual
                    self._visited_cells.append(current_cell)
                    self._creation_stack.append(current_cell)

                elif random_cell == "down":
                    self.move_down(current_cell)
                    self._local_maze_graph.add_edge(current_cell, current_cell + self._rows)
                    current_cell = current_cell + self._rows
                    self.color_one_cell(current_cell)  # visual to show creation
                    time.sleep(CREATE_SPEED)  # pause for effect
                    self.uncolor_one_cell(current_cell)  # erase creation visual
                    self._visited_cells.append(current_cell)
                    self._creation_stack.append(current_cell)

            else:
                current_cell = self._creation_stack.pop()
                self.color_end(current_cell)  # visual to show backtracking
                time.sleep(self._create_speed)  # pause for effect
                self.uncolor_one_cell(current_cell)  # erase creation visual

        # Mark beginning of maze green and end red
        self.color_beginning(1)
        self.color_end(self._global_node_count)

    #  creates mazes that are not shown on the screen (this method was used to construct .gml files that are loaded on
    #  demand to save time for the user as maze creation at 100k nodes take several minutes).
    #  this method is not used for real time running of the program
    def create_the_maze_too_big(self):
        self._creation_stack.append(1)  # starting cell goes into stack
        self._visited_cells.append(1)
        current_cell = 1
        while len(self._creation_stack) > 0:
            cell_list = []
            if current_cell % self._rows != 0 and (current_cell + 1) not in self._visited_cells:
                cell_list.append("right")
            if (current_cell - 1) % self._rows != 0 and (current_cell - 1) not in self._visited_cells:
                cell_list.append("left")
            if (current_cell + self._rows) <= self._global_node_count and (
                    current_cell + self._rows) not in self._visited_cells:
                cell_list.append("down")
            if (current_cell - self._rows) > 0 and (current_cell - self._rows) not in self._visited_cells:
                cell_list.append("up")

            if len(cell_list) > 0:
                random_cell = random.choice(cell_list)
                if random_cell == "right":
                    self._local_maze_graph.add_edge(current_cell, current_cell + 1)
                    current_cell = current_cell + 1
                    self._visited_cells.append(current_cell)
                    self._creation_stack.append(current_cell)

                elif random_cell == "left":
                    self._local_maze_graph.add_edge(current_cell, current_cell - 1)
                    current_cell = current_cell - 1
                    self._visited_cells.append(current_cell)
                    self._creation_stack.append(current_cell)

                elif random_cell == "up":
                    self._local_maze_graph.add_edge(current_cell, current_cell - self._rows)
                    current_cell = current_cell - self._rows
                    self._visited_cells.append(current_cell)
                    self._creation_stack.append(current_cell)

                elif random_cell == "down":
                    self._local_maze_graph.add_edge(current_cell, current_cell + self._rows)
                    current_cell = current_cell + self._rows
                    self._visited_cells.append(current_cell)
                    self._creation_stack.append(current_cell)

            else:
                current_cell = self._creation_stack.pop()

    #  custom depth first search algorithm
    def depth_first_search(self) -> []:
        visited_nodes = set()
        nodes_stack = []
        maze_solution_temp = []
        maze_solution = []
        current_node = 1
        self._dfs_nodes_visited = 1
        current_node_change = 1
        visited_nodes.add(current_node)
        nodes_stack.append(current_node)

        while nodes_stack:
            current_node_change = current_node
            if current_node == self._global_node_count:
                x = len(nodes_stack)
                for i in range(0, x):
                    maze_solution_temp.append(nodes_stack.pop())
                x = len(maze_solution_temp)
                for i in range(0, x):
                    maze_solution.append(maze_solution_temp.pop())
                return maze_solution
            for nbr in self._local_maze_graph.adj[current_node].items():
                if nbr[0] not in visited_nodes:
                    self._dfs_nodes_visited += 1
                    nodes_stack.append(nbr[0])
                    visited_nodes.add(nbr[0])
                    current_node = nbr[0]
                    break
            if current_node_change == current_node:
                nodes_stack.pop()
                current_node = nodes_stack.pop()
                nodes_stack.append(current_node)

        return maze_solution

    #  custom breadth first search algorithm
    def breadth_first_search(self) -> []:
        previous_node_dictionary = {}
        node_queue = [1]
        maze_solution_temp = []
        maze_solution = []
        visited_nodes_set = set()
        visited_nodes_set.add(1)
        self._bfs_nodes_visited = 1
        current_node = 1

        while node_queue:

            if len(node_queue) == 0:
                break
            x = len(node_queue)

            for i in range(0, x):
                current_node = node_queue.pop()
                for nbr in self._local_maze_graph.adj[current_node].items():
                    if nbr[0] not in visited_nodes_set:
                        node_queue.append(nbr[0])
                        visited_nodes_set.add(nbr[0])
                        self._bfs_nodes_visited += 1
                        previous_node_dictionary[nbr[0]] = current_node
                        if nbr[0] == self._global_node_count:
                            #  maze is solved
                            current_node = nbr[0]
                            while True:
                                maze_solution_temp.append(current_node)
                                current_node = previous_node_dictionary.get(current_node)
                                if current_node == 1:
                                    maze_solution_temp.append(1)
                                    x = len(maze_solution_temp)
                                    for m in range(0, x):
                                        maze_solution.append(maze_solution_temp.pop())
                                    return maze_solution
        return maze_solution

    # custom written Dijkstra's algorithm for shortest path, Group 1 COP3530
    # uses some lines of code from Stepik Module 8.2 Dijkstra's Shortest Paths From Source Vertex to all Vertices
    def abbreviated_dijkstra(self) -> []:
        # Dijkstra variables
        priority_queue = []  # heap based on distance array variable
        self._dijkstra_nodes_visited = 1  # count includes starting node 1, count all node visits
        shortest_path = arr.array('i')  # unique node shortest path
        visited_nodes = set()  # set of visited nodes with unique nodes to prevent retracing steps
        distance = arr.array('i', [0, 0])  # map that stores all the distances from the source node
        heapq.heappush(priority_queue, (0, 1))  # add starting node: always start at node 1 and distance 0
        visited_nodes.add(1)  # add starting node: always start at node 1
        ancestor = set()  # store node and ancestor
        origin = 1  # origin set to 1

        i = 2
        while i != (self._global_node_count + 1):
            distance.append(self._global_node_count)  # load each distance in initial map with INT_MAX
            i += 1

        while origin != self._global_node_count:
            for nbr in self._local_maze_graph.adj[origin].items():  # step through neighbors of origin
                if nbr[0] not in visited_nodes:  # except for nodes already visited
                    u = origin  # get current node
                    v = nbr[0]  # neighbor
                    w = 1  # u->v the weight of the edge
                    if distance[v] > (distance[u] + w):
                        distance[v] = distance[u] + w
                        heapq.heappush(priority_queue, (distance[v], v))
                        self._dijkstra_nodes_visited += 1  # increment sumPath
                        visited_nodes.add(v)
                        ancestor.add((v, origin))
            origin = priority_queue[0][1]  # move origin to next item in heap
            heapq.heappop(priority_queue)  # pop item off heap

        # creating shortest path vector (will be reverse order)
        origin = self._global_node_count  # start
        while origin != 1:
            # Find an element in list of tuples.
            for item in ancestor:
                if item[0] == origin:
                    origin = item[1]
                    shortest_path.append(item[0])
        shortest_path.append(origin)

        ascending_order_path = []
        x = len(shortest_path)
        for i in range(0, x):
            ascending_order_path.append(shortest_path.pop())

        return ascending_order_path

    # will execute all 3 algorithms on currently selected maze size (Dijkstra, BFS, DFS)
    # results output visually for smaller mazes, times only for 100k size

    # using custom programmed Dijkstra's, DFS, and BFS algorithms to solve maze
    # report time to execute for each
    # display solution visually on screen and as a vector in console
    def solve_the_maze(self) -> str:
        start_time = time.time_ns()
        self._local_maze_solution_dijkstra = self.abbreviated_dijkstra()
        end_time = time.time_ns()
        self._local_execution_time_dijkstra = (end_time - start_time) / 1000000

        start_time = time.time_ns()
        self._local_maze_solution_dfs = self.depth_first_search()
        end_time = time.time_ns()
        self._local_execution_time_dfs = (end_time - start_time) / 1000000

        start_time = time.time_ns()
        self._local_maze_solution_bfs = self.breadth_first_search()
        end_time = time.time_ns()
        self._local_execution_time_bfs = (end_time - start_time) / 1000000

        shortest_time = self._local_execution_time_dijkstra
        self._local_winning_algo = 'Dijkstra'
        if self._local_execution_time_dijkstra == self._local_execution_time_bfs:
            if self._local_execution_time_dijkstra == self._local_execution_time_dfs:
                self._local_winning_algo = 'It is a tie!'
        if self._local_execution_time_bfs < self._local_execution_time_dijkstra:
            shortest_time = self._local_execution_time_bfs
            self._local_winning_algo = 'Breadth First'
        if self._local_execution_time_dfs < shortest_time:
            self._local_winning_algo = 'Depth First'

        print('The solution to the maze in vector of nodes form: (Dijkstra, then DFS, then BFS)')
        print(self._local_maze_solution_dijkstra)
        print(self._local_maze_solution_dfs)
        print(self._local_maze_solution_bfs)
        self.display_maze_solution(self._local_maze_solution_bfs)
        return self._local_winning_algo

    # solves the maze using Dijkstra's, BFS, DFS, but outputs no visuals as maze of 100k cannot fit on screen
    # shows solve times for each on screen
    def solve_the_maze_too_big(self) -> str:
        start_time = time.time_ns()
        self._local_maze_solution_dijkstra = self.abbreviated_dijkstra()
        end_time = time.time_ns()
        self._local_execution_time_dijkstra = (end_time - start_time) / 1000000

        start_time = time.time_ns()
        self._local_maze_solution_dfs = self.depth_first_search()
        end_time = time.time_ns()
        self._local_execution_time_dfs = (end_time - start_time) / 1000000

        start_time = time.time_ns()
        self._local_maze_solution_bfs = self.breadth_first_search()
        end_time = time.time_ns()
        self._local_execution_time_bfs = (end_time - start_time) / 1000000

        shortest_time = self._local_execution_time_dijkstra
        self._local_winning_algo = 'Dijkstra'
        if self._local_execution_time_dijkstra == self._local_execution_time_bfs:
            if self._local_execution_time_dijkstra == self._local_execution_time_dfs:
                self._local_winning_algo = 'It is a tie!'
        if self._local_execution_time_bfs < self._local_execution_time_dijkstra:
            shortest_time = self._local_execution_time_bfs
            self._local_winning_algo = 'Breadth First'
        if self._local_execution_time_dfs < shortest_time:
            self._local_winning_algo = 'Depth First'

        print('The solution to the maze in vector of nodes form: (Dijkstra, then DFS, then BFS)')
        print(self._local_maze_solution_dijkstra)
        print(self._local_maze_solution_dfs)
        print(self._local_maze_solution_bfs)
        return self._local_winning_algo

    # This method is called to run the maze
    # First, it will determine whether or not the maze will fit on the screen.
    # IF the maze does fit on screen, it will call methods to visualize real time maze creation
    # Then, it will solve the maze using dijkstra's, BFS, DFS, and output results to screen.
    # IF the maze does not fit on screen, it will use the user selected pre-compiled maze to run
    # all algorithms on in the background.  Once solutions are calculated, it will display results
    # to the screen.
    def run_the_maze(self):
        self._visited_cells = []
        self._creation_stack = []
        self._rows = 0
        self._the_screen.fill(BLACK)
        menu.draw(self._the_screen)
        pygame.draw.rect(self._the_screen, GRAY, pygame.Rect(900, 400, 500, 500))
        self._local_maze_graph = nx.Graph()
        pygame.display.update()
        self.define_rows()

        if self._global_node_count <= 1600:
            self.build_maze(self._global_node_count)
            self.create_the_maze()
            time.sleep(2)
            self.solve_the_maze()
            pygame.mixer.Sound.play(end_maze_sound)
            self._solved = True
        else:
            # here we will code the loading for bigger mazes.
            loading_text = font.render("Solving GIGANTIC Maze Number " + str(self._high_nodes_menu_choice), True,
                                       (255, 255, 255))
            loading_text2 = font.render("This might take a second. Please bear with us...", True, (255, 255, 255))
            loading_text3 = font.render("Dijkstra's algorithm is turning your CPU into a space heater", True,
                                        (255, 255, 255))
            self._the_screen.blit(loading_text, (200, 350))
            self._the_screen.blit(loading_text2, (150, 400))
            self._the_screen.blit(loading_text3, (35, 450))
            pygame.display.update()
            if self._high_nodes_menu_choice == 1:  # TODO local_maze_graph may be local variable and cause issues?
                self._local_maze_graph = nx.read_gml("assets/graph100k_ONE.gml", destringizer=int)
            if self._high_nodes_menu_choice == 2:
                self._local_maze_graph = nx.read_gml("assets/graph100k_TWO.gml", destringizer=int)
            if self._high_nodes_menu_choice == 3:
                self._local_maze_graph = nx.read_gml("assets/graph100k_THREE.gml", destringizer=int)
            self.solve_the_maze_too_big()
            self._the_screen.fill(BLACK)
            pygame.mixer.Sound.play(end_maze_sound)
            loading_text = font.render("Solved!", True, (255, 255, 255))
            self._the_screen.blit(loading_text, (395, 450))

            self._solved = True

    # method to set node count of maze based on user input via menu
    # depending on number of nodes selected, various menu features should be turned on/off
    # for user interaction
    # specifically, if node count == 100k, turn off visual speed sliders as they are irrelevant
    # if node count <= 1600, turn on visual sliders, but disable precompiled graph selection
    def set_node_count(self, selected: Tuple, value: Any) -> None:
        if value == 1:
            self._global_node_count = 49
            btn.readonly = True
            btn.is_selectable = False
            slider.readonly = False
            slider.is_selectable = True
            slider2.readonly = False
            slider2.is_selectable = True
        if value == 2:
            self._global_node_count = 900
            btn.readonly = True
            btn.is_selectable = False
            slider.readonly = False
            slider.is_selectable = True
            slider2.readonly = False
            slider2.is_selectable = True
        if value == 3:
            self._global_node_count = 1600
            btn.readonly = True
            btn.is_selectable = False
            slider.readonly = False
            slider.is_selectable = True
            slider2.readonly = False
            slider2.is_selectable = True
        if value == 4:
            self._global_node_count = 100000
            self._solve_speed = 0
            btn.readonly = False
            btn.is_selectable = True
            slider.readonly = True
            slider.is_selectable = False
            slider2.readonly = True
            slider2.is_selectable = False

    # will set creation maze delay for faster/slower creation depending on user preference, set via slider on menu
    def set_creation_speed(self, x):
        self._create_speed = x

    # sets maze solution visualization speed faster/slower based on user input from slider
    def set_solve_speed(self, x):
        self._solve_speed = x

    # sets user choice of 100k size maze (select from 3 possibilities),
    # sets variable high nodes menu choice equal to same
    def menu_choice(self, x, y):
        self._high_nodes_menu_choice = y

    # getters and setters:

    # return if maze is solved or not
    def is_solved(self):
        return self._solved

    # number of nodes visited by dijkstra to find solution
    def dijkstra_nodes(self):
        return self._dijkstra_nodes_visited

    # number of nodes visited by DFS to find solution
    def dfs_nodes(self):
        return self._dfs_nodes_visited

    # number of nodes visited by BFS to find solution
    def bfs_nodes(self):
        return self._bfs_nodes_visited

    # time taken to solve via Dijkstra's algorithm
    def dijkstra_time(self):
        return self._local_execution_time_dijkstra

    # time taken to solve by BFS algorithms
    def bfs_time(self):
        return self._local_execution_time_bfs

    # time taken to solve by DFS
    def dfs_time(self):
        return self._local_execution_time_dfs

    # number of nodes in solution path solved via Dijkstra's
    def dijkstra_solution(self):
        return len(self._local_maze_solution_dijkstra)

    # number of nodes in solution path solved via DFS
    def bfs_solution(self):
        return len(self._local_maze_solution_bfs)

    # number of nodes in solution path solved via DFS
    def dfs_solution(self):
        return len(self._local_maze_solution_dfs)

    # algorithm with the shortest run time returned via string
    def winning_algorithm(self):
        return self._local_winning_algo


# class button used to display buttons on main menu screen
class Button:
    def __init__(self, the_screen, image, pos, text_input, button_font, base_color, hovering_color):
        self.image = image
        self.x_pos = pos[0]
        self.y_pos = pos[1]
        self.font = button_font
        self.base_color, self.hovering_color = base_color, hovering_color
        self.text_input = text_input
        self.text = self.font.render(self.text_input, True, self.base_color)
        if self.image is None:
            self.image = self.text
        self.rect = self.image.get_rect(center=(self.x_pos, self.y_pos))
        self.text_rect = self.text.get_rect(center=(self.x_pos, self.y_pos))
        self.the_screen = the_screen

    def update(self, the_screen):
        if self.image is not None:
            the_screen.blit(self.image, self.rect)
        the_screen.blit(self.text, self.text_rect)

    def check_for_input(self, position):
        if position[0] in range(self.rect.left, self.rect.right) and position[1] in range(self.rect.top,
                                                                                          self.rect.bottom):
            return True
        return False

    def change_color(self, position):
        if position[0] in range(self.rect.left, self.rect.right) and position[1] in range(self.rect.top,
                                                                                          self.rect.bottom):
            self.text = self.font.render(self.text_input, True, self.hovering_color)
        else:
            self.text = self.font.render(self.text_input, True, self.base_color)


# set up pygame window
WIDTH = 1400  # size of pygame window
HEIGHT = 900
FPS = 30  # FPS pygame running at natively
GRAPH_X_OFFSET = 30  # for adjusting offset of top left corner of graph
GRAPH_Y_OFFSET = 25  # for adjusting offset of top left corner of graph
GRAPH_SCALE_FACTOR = 1  # option to scale graph - no current user options for this, but allows for future expansion
CREATE_SPEED = .001  # how fast visuals show maze creation on screen
SOLVE_SPEED = .1  # how fast visuals show maze solution on screen

# Define colors (Self explanatory)
WHITE = (255, 255, 255)
GREEN = (0, 255, 0,)
BLUE = (0, 0, 255)
YELLOW = (255, 255, 0)
BLACK = (0, 0, 0)
RED = (255, 0, 0)
GRAY = (107, 107, 107)

# initialise Pygame
pygame.init()
pygame.mixer.init()  # get some music in da club
screen = pygame.display.set_mode((WIDTH, HEIGHT))  # set size of screen
pygame.font.init()  # get some fonts
font = pygame.font.SysFont('Comic Sans MS', 30)  # i choose you, comic sans MS
clock = pygame.time.Clock()  # initialize clock for time keeping

# set the mood with some MUSIC! also loads sound effects
solve_click = pygame.mixer.Sound("assets/click.wav")  # sound effect for blocks solving maze
end_maze_sound = pygame.mixer.Sound("assets/Success.mp3")  # sound effect for successful maze solution on screen
pygame.mixer.music.load('assets/Intro-Music.mp3')  # title screen music
pygame.mixer.music.set_volume(0.1)  # volume of music
pygame.mixer.music.play(-1)


def get_font(size):  # Returns font choice
    return pygame.font.Font("assets/font.ttf", size)


# this is the 'about' page accessible via the main menu to display credits of authors
def options(the_screen):
    the_screen = pygame.display.set_mode((WIDTH, HEIGHT))
    background_options = pygame.image.load("assets/UF.png")
    while True:
        screen.fill((230, 230, 250))
        screen.blit(background_options, (0, 0))
        options_mouse_pos = pygame.mouse.get_pos()

        options_text = get_font(45).render("Created by:", True, "WHITE")
        options_rect = options_text.get_rect(center=(650, 100))

        zak_text = get_font(45).render("Zachary Schirm", True, "WHITE")
        zak_rect = options_text.get_rect(center=(650, 220))

        aaron_text = get_font(45).render("Aaron Hamburger", True, "WHITE")
        aaron_rect = options_text.get_rect(center=(650, 300))

        serg_text = get_font(45).render("Sergio Arcila", True, "WHITE")
        serg_rect = options_text.get_rect(center=(650, 380))

        uf_text = get_font(45).render("UFL COP3530 FINAL PROJECT", True, "WHITE")
        uf_rect = options_text.get_rect(center=(400, 600))

        screen.blit(options_text, options_rect)
        screen.blit(aaron_text, aaron_rect)
        screen.blit(zak_text, zak_rect)
        screen.blit(serg_text, serg_rect)
        screen.blit(zak_text, zak_rect)
        screen.blit(uf_text, uf_rect)

        options_back = Button(screen, image=None, pos=(700, 800),
                              text_input="BACK", button_font=get_font(75), base_color="Black",
                              hovering_color="Green")

        options_back.change_color(options_mouse_pos)
        options_back.update(screen)

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit()
                sys.exit()
            if event.type == pygame.MOUSEBUTTONDOWN:
                if options_back.check_for_input(options_mouse_pos):
                    main_menu()

        pygame.display.update()


# outlines main menu text
def draw_outline(x, y, string, col, size, window):
    font = pygame.font.Font("assets/font.ttf", size)
    text = font.render(string, True, col)
    textbox = text.get_rect()
    textbox.center = (x, y)
    window.blit(text, textbox)


# display main menu
def main_menu():
    pygame.mixer.music.load('assets/maze-music.wav')
    pygame.mixer.music.set_volume(0.05)
    pygame.mixer.music.play(-1)
    screen = pygame.display.set_mode((WIDTH, HEIGHT))
    pygame.display.set_caption("Mighty Maze Magicians Present: The Magical Maze Solver!")

    background = pygame.image.load("assets/Maze.jpg")

    while True:
        screen.blit(background, (0, 0))

        mouse = pygame.mouse.get_pos()

        menu_text = get_font(60).render("THE MAGICAL MAZE SOLVER", True, "#b68f40")
        welcome_text = get_font(60).render("WELCOME TO", True, "#b68f40")
        menu_rect = menu_text.get_rect(center=(700, 220))
        welcome_rect = welcome_text.get_rect(center=(700, 100))
        x = 700
        y = 220
        draw_outline(x + 3, y - 2, "THE MAGICAL MAZE SOLVER", BLACK, 60, screen)
        # top right
        draw_outline(x + 5, y - 4, "THE MAGICAL MAZE SOLVER", BLACK, 60, screen)

        y2 = 100
        draw_outline(x + 3, y2 - 2, "WELCOME TO", BLACK, 60, screen)
        # top right
        draw_outline(x + 5, y2 - 4, "WELCOME TO", BLACK, 60, screen)

        play_button = Button(screen, image=pygame.image.load("assets/Options Rect.png"), pos=(700, 500),
                             text_input="PLAY", button_font=get_font(60), base_color="#86f67d", hovering_color="White")
        options_button = Button(screen, image=pygame.image.load("assets/quit Rect.png"), pos=(200, 700),
                                text_input="CREDITS", button_font=get_font(49), base_color="#d7fcd4",
                                hovering_color="White")
        quit_button = Button(screen, image=pygame.image.load("assets/Quit Rect.png"), pos=(1200, 700),
                             text_input="QUIT", button_font=get_font(55), base_color="#e8351a", hovering_color="White")

        screen.blit(menu_text, menu_rect)
        screen.blit(welcome_text, welcome_rect)

        for button in [play_button, options_button, quit_button]:
            button.change_color(mouse)
            button.update(screen)

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit()
                sys.exit()
            if event.type == pygame.MOUSEBUTTONDOWN:
                if play_button.check_for_input(mouse):
                    the_main_maze()
                if options_button.check_for_input(mouse):
                    options(screen)
                if quit_button.check_for_input(mouse):
                    pygame.quit()
                    sys.exit()

        pygame.display.update()


# This will display and run the main maze/program screen in pygame including displaying options menu in top right corner
def the_main_maze():
    the_screen = pygame.display.set_mode((WIDTH, HEIGHT))
    pygame.display.set_caption("WHICH ALGORITHM WILL BE BEST?")
    maze_back_ground = pygame.image.load("assets/Options.png")
    the_screen.blit(maze_back_ground, (0, 0))

    # pygame loop
    game_on = True
    while game_on:
        clock.tick(FPS)
        events = pygame.event.get()
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                game_on = False
            if event.type == pygame.MOUSEBUTTONDOWN:
                continue

        if menu.is_enabled():
            menu.update(events)
            menu.draw(screen)

        pygame.draw.rect(screen, GRAY, pygame.Rect(900, 400, 500, 500))

        if this_maze.is_solved():
            dijkstra_text = font.render('Dijkstra: ', True, (0, 0, 0))
            dijkstra_nodes = font.render("Nodes Visited: " + str(this_maze.dijkstra_nodes()), True, (0, 0, 0))
            dijkstra_solution_nodes = font.render("Nodes in Solution: " + str(this_maze.dijkstra_solution()), True,
                                                  (0, 0, 0))
            dijkstra_solve = font.render("Time to solve (ms): " + str(this_maze.dijkstra_time()), True, (0, 0, 0))

            dfs_text = font.render('Depth First Search: ', True, (0, 0, 0))
            dfs_nodes = font.render("Nodes Visited: " + str(this_maze.dfs_nodes()), True, (0, 0, 0))
            dfs_solution_nodes = font.render("Nodes in Solution: " + str(this_maze.dfs_solution()), True, (0, 0, 0))
            dfs_solve = font.render("Time to solve (ms): " + str(this_maze.dfs_time()), True, (0, 0, 0))

            bfs_text = font.render('Breadth First Search: ', True, (0, 0, 0))
            bfs_nodes = font.render("Nodes Visited: " + str(this_maze.bfs_nodes()), True, (0, 0, 0))
            bfs_solution_nodes = font.render("Nodes in Solution: " + str(this_maze.bfs_solution()), True, (0, 0, 0))
            bfs_solve = font.render("Time to solve (ms): " + str(this_maze.bfs_time()), True, (0, 0, 0))

            winner = font.render('Fastest Algorithm: ', True, (0, 0, 0))
            font_winner = font.render(this_maze.winning_algorithm(), True, (0, 0, 0))

            screen.blit(dijkstra_text, (900, 400))
            screen.blit(dijkstra_solve, (950, 430))
            screen.blit(dijkstra_nodes, (950, 460))
            screen.blit(dijkstra_solution_nodes, (950, 490))

            screen.blit(dfs_text, (900, 550))
            screen.blit(dfs_solve, (950, 580))
            screen.blit(dfs_nodes, (950, 610))
            screen.blit(dfs_solution_nodes, (950, 640))

            screen.blit(bfs_text, (900, 700))
            screen.blit(bfs_solve, (950, 730))
            screen.blit(bfs_nodes, (950, 760))
            screen.blit(bfs_solution_nodes, (950, 790))

            screen.blit(winner, (900, 840))
            screen.blit(font_winner, (1180, 840))

        for event in pygame.event.get():
            if event.type == pygame.locals.QUIT:
                pygame.quit()
                sys.exit()
            if event.type == pygame.KEYDOWN:
                if event.key == pygame.K_ESCAPE:
                    pygame.quit()

        pygame.display.update()


# setup size of menu in top right corner of pygame menu
menu = pygame_menu.Menu(
    height=400,
    width=500,
    mouse_motion_selection=True,
    position=(900, 0, False),
    theme=pygame_menu.themes.THEME_DARK,
    title='OPTIONS',
)

# create instance of maze class
this_maze = Maze(screen, font, GRAPH_SCALE_FACTOR, SOLVE_SPEED, CREATE_SPEED)

# construct pygame menu for top right corner of main maze page
font_size_menu = 25
menu.add.selector('Maze Node Count: ', [('49', 1), ('900', 2), ('1,600', 3), ('100,000', 4)],
                  onchange=this_maze.set_node_count, font_size=font_size_menu)
btn = menu.add.selector('Large Maze Choices: ', [('Graph 1', 1), ('Graph 2', 2), ('Graph 3', 3)],
                        onchange=this_maze.menu_choice, font_size=font_size_menu)
btn.readonly = True
btn.is_selectable = False
menu.add.label("----Speed Adjustment (Visuals)----", label_id="label_widget", font_size=font_size_menu)
slider = menu.add.range_slider("Maze Creation Delay:", rangeslider_id="creation_speed_slider", default=.001,
                               range_values=(0, 0.1), increment=10, onchange=this_maze.set_creation_speed,
                               font_size=font_size_menu)
slider.readonly = False
slider.is_selectable = True
slider2 = menu.add.range_slider("Maze Solution Delay:", rangeslider_id="solve_speed_slider",
                                default=.1, range_values=(0, 0.1), increment=10, onchange=this_maze.set_solve_speed,
                                font_size=font_size_menu)
slider2.readonly = False
slider2.is_selectable = True

menu.add.button('Start Maze', this_maze.run_the_maze, font_size=font_size_menu)

menu.add.button('Back to Main Menu', main_menu, font_size=font_size_menu)

# entry point to the program - display main menu
main_menu()

# Attributions:
# Free sounds/music from zapsplat.com
# Royalty free images from pixabay.com
# 8.2 Dijkstra's Shortest Paths From Source Vertex to all Vertices
#
# inspiration for maze creation visuals and recursive
# back-tracker algorithm from https://www.youtube.com/watch?v=Xthh4SEMA2o
