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


class Button():
    def __init__(self, image, pos, text_input, font, base_color, hovering_color):
        self.image = image
        self.x_pos = pos[0]
        self.y_pos = pos[1]
        self.font = font
        self.base_color, self.hovering_color = base_color, hovering_color
        self.text_input = text_input
        self.text = self.font.render(self.text_input, True, self.base_color)
        if self.image is None:
            self.image = self.text
        self.rect = self.image.get_rect(center=(self.x_pos, self.y_pos))
        self.text_rect = self.text.get_rect(center=(self.x_pos, self.y_pos))

    def update(self, screen):
        if self.image is not None:
            screen.blit(self.image, self.rect)
        screen.blit(self.text, self.text_rect)

    def checkForInput(self, position):
        if position[0] in range(self.rect.left, self.rect.right) and position[1] in range(self.rect.top,
                                                                                          self.rect.bottom):
            return True
        return False

    def changeColor(self, position):
        if position[0] in range(self.rect.left, self.rect.right) and position[1] in range(self.rect.top,
                                                                                          self.rect.bottom):
            self.text = self.font.render(self.text_input, True, self.hovering_color)
        else:
            self.text = self.font.render(self.text_input, True, self.base_color)


# create a new graph using networkx package
global mazeGraph
mazeGraph = nx.Graph()


# set up pygame window
WIDTH = 1400
HEIGHT = 900
FPS = 30
GRAPH_X_OFFSET = 30
GRAPH_Y_OFFSET = 25
GRAPH_SCALE_FACTOR = 1
CREATE_SPEED = .001
SOLVE_SPEED = .1


# declare variables
global execution_time_dijkstra
execution_time_dijkstra = 0
global execution_time_DFS
execution_time_DFS = 0
global execution_time_BFS
execution_time_BFS = 0
global execution_time_bellman
execution_time_bellman = 0
global maze_solution_dijkstra
maze_solution_dijkstra = []
global maze_solution_DFS
maze_solution_bellman = []
global solved
solved = False
global high_nodes
high_nodes = False
global graph_selection
global high_nodes_menu_choice
global DFS_nodes_visited
high_nodes_menu_choice = 1
global maze_solution_BFS
global BFS_visited_nodes
global sumPath
global winning_algo


# Define colors
WHITE = (255, 255, 255)
GREEN = (0, 255, 0,)
BLUE = (0, 0, 255)
YELLOW = (255, 255, 0)
BLACK = (0, 0, 0)
RED = (255, 0, 0)
GRAY = (107, 107, 107)


# initialise Pygame
pygame.init()
pygame.mixer.init()
screen = pygame.display.set_mode((WIDTH, HEIGHT))


# setup maze parameters
visited_cells = []
creation_stack = []
global_node_count = 49  # user input this value
rows = 0


def get_font(size):  # Returns in the desired size
    return pygame.font.Font("assets/font.ttf", size)


# initialize pygame menu
def theMainMaze():
    screen = pygame.display.set_mode((WIDTH, HEIGHT))
    pygame.display.set_caption("WHICH ALGORITHM WILL BE BEST?")
    clock = pygame.time.Clock()
    mazeBackGround = pygame.image.load("assets/Options.png")
    screen.blit(mazeBackGround, (0, 0))
    pygame.font.init()
    font = pygame.font.SysFont('Comic Sans MS', 30)

    # based on user selected maze size, determines number of rows in the maze
    def define_rows():
        global rows
        rows = math.sqrt(global_node_count)  # the global node count needs to be perfect square to make cubic maze
        rows = int(rows)  # wants to give float value - need int - casting to same

    # method to construct maze grid of squares
    def build_maze(node_count):

        # add node_number (user input) of nodes to mazeGraph graph (networkx)
        for i in range(1, node_count + 1):
            mazeGraph.add_node(i)

        # draw background color of maze
        pygame.draw.rect(screen, BLUE, pygame.Rect(GRAPH_X_OFFSET + 20, GRAPH_Y_OFFSET + 20,
                                                   GRAPH_SCALE_FACTOR * 20 * rows, GRAPH_SCALE_FACTOR * 20 * rows))

        # draw all individual cells (Rects), walls will overlap but will be drawn over during maze creation
        for j in range(0, rows):
            for k in range(0, rows):
                pygame.draw.rect(screen, WHITE, pygame.Rect((20 + GRAPH_X_OFFSET + j * 20 * GRAPH_SCALE_FACTOR),
                                                            (20 + GRAPH_Y_OFFSET + k * 20 * GRAPH_SCALE_FACTOR),
                                                            20 * GRAPH_SCALE_FACTOR, 20 * GRAPH_SCALE_FACTOR), width=1)

        # refresh display with above
        pygame.display.update()

    # The following methods are used to 'clear' the maze visually as it is constructed and edges
    # are added between nodes per the algorithm we are using.  The walls are not actually being deleted but
    # rather new rectangles are being drawn over the maze to 'clear' the walls (much easier, looks fine)

    # clear wall upward
    def move_up(node_number):
        if node_number % rows == 0:
            x_pos = rows
            y_pos = int(node_number / (rows + 1))
        else:
            x_pos = int(node_number % rows)
            y_pos = int(node_number / rows)
        pygame.draw.rect(screen, BLUE, pygame.Rect(x_pos * 20 * GRAPH_SCALE_FACTOR + 1 + GRAPH_X_OFFSET,
                                                   y_pos * 20 * GRAPH_SCALE_FACTOR + 1 + GRAPH_Y_OFFSET,
                                                   18 * GRAPH_SCALE_FACTOR, 38 * GRAPH_SCALE_FACTOR))
        pygame.display.update()

    # clear wall rightward
    def move_right(node_number):
        if node_number % rows == 0:
            x_pos = rows
            y_pos = int(node_number / (rows + 1))
        else:
            x_pos = int(node_number % rows)
            y_pos = int(node_number / rows)
        pygame.draw.rect(screen, BLUE, pygame.Rect(x_pos * 20 * GRAPH_SCALE_FACTOR + 1 + GRAPH_X_OFFSET,
                                                   y_pos * 20 * GRAPH_SCALE_FACTOR + 21 + GRAPH_Y_OFFSET,
                                                   38 * GRAPH_SCALE_FACTOR, 18 * GRAPH_SCALE_FACTOR))
        pygame.display.update()

    # clear wall leftward
    def move_left(node_number):
        if node_number % rows == 0:
            x_pos = rows
            y_pos = int(node_number / (rows + 1))
        else:
            x_pos = int(node_number % rows)
            y_pos = int(node_number / rows)
        pygame.draw.rect(screen, BLUE, pygame.Rect(x_pos * 20 * GRAPH_SCALE_FACTOR - 19 + GRAPH_X_OFFSET,
                                                   y_pos * 20 * GRAPH_SCALE_FACTOR + 21 + GRAPH_Y_OFFSET * GRAPH_SCALE_FACTOR,
                                                   38 * GRAPH_SCALE_FACTOR, 18 * GRAPH_SCALE_FACTOR))
        pygame.display.update()

    # clear wall downward
    def move_down(node_number):
        if node_number % rows == 0:
            x_pos = rows
            y_pos = int(node_number / (rows + 1))
        else:
            x_pos = int(node_number % rows)
            y_pos = int(node_number / rows)
        pygame.draw.rect(screen, BLUE, pygame.Rect(x_pos * 20 * GRAPH_SCALE_FACTOR + 1 + GRAPH_X_OFFSET,
                                                   y_pos * 20 * GRAPH_SCALE_FACTOR + 21 + GRAPH_Y_OFFSET,
                                                   18 * GRAPH_SCALE_FACTOR, 38 * GRAPH_SCALE_FACTOR))
        pygame.display.update()

    # color individual cell (for showing maze construction/tracking)
    def color_one_cell(node_number):
        if node_number % rows == 0:
            x_pos = rows
            y_pos = int(node_number / (rows + 1))
        else:
            x_pos = int(node_number % rows)
            y_pos = int(node_number / rows)
        pygame.draw.rect(screen, YELLOW, pygame.Rect(x_pos * 20 * GRAPH_SCALE_FACTOR + 1 + GRAPH_X_OFFSET,
                                                     y_pos * 20 * GRAPH_SCALE_FACTOR + 21 + GRAPH_Y_OFFSET,
                                                     18 * GRAPH_SCALE_FACTOR, 18 * GRAPH_SCALE_FACTOR))
        pygame.display.update()

    # will color beginning cell of maze GREEN
    def color_beginning(node_number):
        if node_number % rows == 0:
            x_pos = rows
            y_pos = int(node_number / (rows + 1))
        else:
            x_pos = int(node_number % rows)
            y_pos = int(node_number / rows)
        pygame.draw.rect(screen, GREEN, pygame.Rect(x_pos * 20 * GRAPH_SCALE_FACTOR + 1 + GRAPH_X_OFFSET,
                                                    y_pos * 20 * GRAPH_SCALE_FACTOR + 21 + GRAPH_Y_OFFSET,
                                                    18 * GRAPH_SCALE_FACTOR, 18 * GRAPH_SCALE_FACTOR))
        pygame.display.update()

    # will color end cell of maze RED
    def color_end(node_number):
        if node_number % rows == 0:
            x_pos = rows
            y_pos = int(node_number / (rows + 1))
        else:
            x_pos = int(node_number % rows)
            y_pos = int(node_number / rows)
        pygame.draw.rect(screen, RED, pygame.Rect(x_pos * 20 * GRAPH_SCALE_FACTOR + 1 + GRAPH_X_OFFSET,
                                                  y_pos * 20 * GRAPH_SCALE_FACTOR + 21 + GRAPH_Y_OFFSET,
                                                  18 * GRAPH_SCALE_FACTOR, 18 * GRAPH_SCALE_FACTOR))
        pygame.display.update()

    # return highlighted cell to original color
    # this is used when showing that the maze generating algorithms is 'backtracking'
    # to find the next node in stack with unvisited nodes
    def uncolor_one_cell(node_number):
        if node_number % rows == 0:
            x_pos = rows
            y_pos = int(node_number / (rows + 1))
        else:
            x_pos = int(node_number % rows)
            y_pos = int(node_number / rows)
        pygame.draw.rect(screen, BLUE, pygame.Rect(x_pos * 20 * GRAPH_SCALE_FACTOR + 1 + GRAPH_X_OFFSET,
                                                   y_pos * 20 * GRAPH_SCALE_FACTOR + 21 + GRAPH_Y_OFFSET,
                                                   18 * GRAPH_SCALE_FACTOR, 18 * GRAPH_SCALE_FACTOR))
        pygame.display.update()

    # solution cell that shows small box in center to mark path/solution
    def show_solution_cell(node_number):
        if node_number % rows == 0:
            x_pos = rows
            y_pos = int(node_number / (rows + 1))
        else:
            x_pos = int(node_number % rows)
            y_pos = int(node_number / rows)
        pygame.draw.rect(screen, WHITE, pygame.Rect(x_pos * 20 * GRAPH_SCALE_FACTOR + 8 + GRAPH_X_OFFSET,
                                                    y_pos * 20 * GRAPH_SCALE_FACTOR + 28 + GRAPH_Y_OFFSET,
                                                    3 * GRAPH_SCALE_FACTOR, 3 * GRAPH_SCALE_FACTOR))
        pygame.display.update()

    # method to show the solution to the maze visually
    def display_maze_solution(maze_solution):
        for i in maze_solution:
            show_solution_cell(i)
            pygame.mixer.Sound.play(solve_click)
            time.sleep(SOLVE_SPEED)

    # this is the back-racker algorithm we discussed to generate the maze randomly
    # basically, it takes a node and determines how many UNVISITED neighbors in the maze it has that can be
    # travelled to.  It will randomly select one of those, break down the wall between it, then add an edge in the graph
    # between those nodes.  A stack is created of all previously visited nodes in case a dead end is reached, in which case
    # the loop will pop nodes off the stack until a node with unvisited neighbors is found and then continue
    # construction of the maze.
    def create_the_maze():
        creation_stack.append(1)  # starting cell goes into stack
        visited_cells.append(1)
        current_cell = 1
        while len(creation_stack) > 0:
            time.sleep(CREATE_SPEED)
            cell_list = []
            if current_cell % rows != 0 and (current_cell + 1) not in visited_cells:
                cell_list.append("right")
            if (current_cell - 1) % rows != 0 and (current_cell - 1) not in visited_cells:
                cell_list.append("left")
            if (current_cell + rows) <= global_node_count and (current_cell + rows) not in visited_cells:
                cell_list.append("down")
            if (current_cell - rows) > 0 and (current_cell - rows) not in visited_cells:
                cell_list.append("up")

            if len(cell_list) > 0:
                random_cell = random.choice(cell_list)
                if random_cell == "right":
                    move_right(current_cell)
                    mazeGraph.add_edge(current_cell, current_cell + 1)
                    current_cell = current_cell + 1
                    color_one_cell(current_cell)  # visual to show backtracking
                    time.sleep(CREATE_SPEED)  # pause for effect
                    uncolor_one_cell(current_cell)  # erase backtracking visual
                    visited_cells.append(current_cell)
                    creation_stack.append(current_cell)

                elif random_cell == "left":
                    move_left(current_cell)
                    mazeGraph.add_edge(current_cell, current_cell - 1)
                    current_cell = current_cell - 1
                    color_one_cell(current_cell)  # visual to show backtracking
                    time.sleep(CREATE_SPEED)  # pause for effect
                    uncolor_one_cell(current_cell)  # erase backtracking visual
                    visited_cells.append(current_cell)
                    creation_stack.append(current_cell)

                elif random_cell == "up":
                    move_up(current_cell)
                    mazeGraph.add_edge(current_cell, current_cell - rows)
                    current_cell = current_cell - rows
                    color_one_cell(current_cell)  # visual to show backtracking
                    time.sleep(CREATE_SPEED)  # pause for effect
                    uncolor_one_cell(current_cell)  # erase backtracking visual
                    visited_cells.append(current_cell)
                    creation_stack.append(current_cell)

                elif random_cell == "down":
                    move_down(current_cell)
                    mazeGraph.add_edge(current_cell, current_cell + rows)
                    current_cell = current_cell + rows
                    color_one_cell(current_cell)  # visual to show backtracking
                    time.sleep(CREATE_SPEED)  # pause for effect
                    uncolor_one_cell(current_cell)  # erase backtracking visual
                    visited_cells.append(current_cell)
                    creation_stack.append(current_cell)

            else:
                current_cell = creation_stack.pop()
                color_end(current_cell)  # visual to show backtracking
                time.sleep(CREATE_SPEED)  # pause for effect
                uncolor_one_cell(current_cell)  # erase backtracking visual

        # Mark beginning of maze green and end red
        color_beginning(1)
        color_end(global_node_count)

    #  creates mazes that are not shown on the screen (this method was used to construct .gml files that are loaded on
    #  demand to save time for the user as maze creation at 100k nodes take several minutes).
    #  this method is not used for real time running of the program
    def create_the_maze_too_big():
        creation_stack.append(1)  # starting cell goes into stack
        visited_cells.append(1)
        current_cell = 1
        while len(creation_stack) > 0:
            cell_list = []
            if current_cell % rows != 0 and (current_cell + 1) not in visited_cells:
                cell_list.append("right")
            if (current_cell - 1) % rows != 0 and (current_cell - 1) not in visited_cells:
                cell_list.append("left")
            if (current_cell + rows) <= global_node_count and (current_cell + rows) not in visited_cells:
                cell_list.append("down")
            if (current_cell - rows) > 0 and (current_cell - rows) not in visited_cells:
                cell_list.append("up")

            if len(cell_list) > 0:
                random_cell = random.choice(cell_list)
                if random_cell == "right":
                    mazeGraph.add_edge(current_cell, current_cell + 1)
                    current_cell = current_cell + 1
                    visited_cells.append(current_cell)
                    creation_stack.append(current_cell)

                elif random_cell == "left":
                    mazeGraph.add_edge(current_cell, current_cell - 1)
                    current_cell = current_cell - 1
                    visited_cells.append(current_cell)
                    creation_stack.append(current_cell)

                elif random_cell == "up":
                    mazeGraph.add_edge(current_cell, current_cell - rows)
                    current_cell = current_cell - rows
                    visited_cells.append(current_cell)
                    creation_stack.append(current_cell)

                elif random_cell == "down":
                    mazeGraph.add_edge(current_cell, current_cell + rows)
                    current_cell = current_cell + rows
                    visited_cells.append(current_cell)
                    creation_stack.append(current_cell)

            else:
                current_cell = creation_stack.pop()

    # using custom programmed Dijkstra's, DFS, and BFS algorithms to solve maze
    # report time to execute for each
    # display solution visually ons creen and as a vector in console
    def solve_the_maze():
        global execution_time_dijkstra
        global execution_time_BFS
        global execution_time_DFS
        global maze_solution_dijkstra
        global maze_solution_DFS
        global maze_solution_BFS
        global winning_algo

        maze_solution_dijkstra = []
        maze_solution_DFS = []
        maze_solution_BFS = []

        start_time = time.time_ns()
        maze_solution_dijkstra = abbreviatedDijkstra()
        end_time = time.time_ns()
        execution_time_dijkstra = (end_time - start_time) / 1000000

        start_time = time.time_ns()
        maze_solution_DFS = depth_first_search()
        end_time = time.time_ns()
        execution_time_DFS = (end_time - start_time) / 1000000

        start_time = time.time_ns()
        maze_solution_BFS = breadth_first_search()
        end_time = time.time_ns()
        execution_time_BFS = (end_time - start_time) / 1000000

        shortest_time = execution_time_dijkstra
        winning_algo = 'Dijkstra'
        if execution_time_dijkstra == execution_time_BFS:
            if execution_time_dijkstra == execution_time_DFS:
                winning_algo = 'It is a tie!'
        if execution_time_BFS < execution_time_dijkstra:
            shortest_time = execution_time_BFS
            winning_algo = 'Breadth First'
        if execution_time_DFS < shortest_time:
            shortest_time = execution_time_DFS
            winning_algo = 'Depth First'

        print('The solution to the maze in vector of nodes form: (Dijkstra, then DFS, then BFS)')
        print(maze_solution_dijkstra)
        print(maze_solution_DFS)
        print(maze_solution_BFS)
        display_maze_solution(maze_solution_BFS)

    # solves the maze using Dijkstra's, BFS, DFS, but outputs no visuals as maze of 100k cannot fit on screen
    # shows solve times for each on screen
    def solve_the_maze_too_big():
        global execution_time_dijkstra
        global execution_time_BFS
        global execution_time_DFS
        global maze_solution_dijkstra
        global maze_solution_DFS
        global maze_solution_BFS
        global winning_algo

        maze_solution_dijkstra = []
        maze_solution_DFS = []
        maze_solution_BFS = []

        start_time = time.time_ns()
        maze_solution_dijkstra = abbreviatedDijkstra()
        maze_solution_dijkstra
        end_time = time.time_ns()
        execution_time_dijkstra = (end_time - start_time) / 1000000
        print('Dijkstras algorithm took:', execution_time_dijkstra, 'ns to execute')

        start_time = time.time_ns()
        maze_solution_DFS = depth_first_search()
        end_time = time.time_ns()
        execution_time_DFS = (end_time - start_time) / 1000000

        start_time = time.time_ns()
        maze_solution_BFS = breadth_first_search()
        end_time = time.time_ns()
        execution_time_BFS = (end_time - start_time) / 1000000

        shortest_time = execution_time_dijkstra
        winning_algo = 'Dijkstra'
        if execution_time_dijkstra == execution_time_BFS:
            if execution_time_dijkstra == execution_time_DFS:
                winning_algo = 'It is a tie!'
        if execution_time_BFS < execution_time_dijkstra:
            shortest_time = execution_time_BFS
            winning_algo = 'Breadth First'
        if execution_time_DFS < shortest_time:
            shortest_time = execution_time_DFS
            winning_algo = 'Depth First'

        print('The solution to the maze in vector of nodes form: (Dijkstra, then DFS, then BFS)')
        print(maze_solution_dijkstra)
        print(maze_solution_DFS)
        print(maze_solution_BFS)

    #  custom depth first search algorithm
    def depth_first_search() -> []:
        global DFS_nodes_visited
        visited_nodes = set()
        nodes_stack = []
        maze_solution_temp = []
        maze_solution = []
        current_node = 1
        DFS_nodes_visited = 1
        current_node_change = 1
        visited_nodes.add(current_node)
        nodes_stack.append(current_node)

        while nodes_stack:
            current_node_change = current_node
            if current_node == global_node_count:
                x = len(nodes_stack)
                for i in range(0, x):
                    maze_solution_temp.append(nodes_stack.pop())
                x = len(maze_solution_temp)
                for i in range(0, x):
                    maze_solution.append(maze_solution_temp.pop())
                return maze_solution
            for nbr in mazeGraph.adj[current_node].items():
                if nbr[0] not in visited_nodes:
                    DFS_nodes_visited += 1
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
    def breadth_first_search() -> []:
        previous_node_dictionary = {}
        node_queue = [1]
        maze_solution_temp = []
        maze_solution = []
        visited_nodes_set = set()
        visited_nodes_set.add(1)
        global BFS_visited_nodes
        BFS_visited_nodes = 1
        current_node = 1

        while node_queue:

            if len(node_queue) == 0:
                break
            x = len(node_queue)

            for i in range(0, x):
                current_node = node_queue.pop()
                for nbr in mazeGraph.adj[current_node].items():
                    if nbr[0] not in visited_nodes_set:
                        node_queue.append(nbr[0])
                        visited_nodes_set.add(nbr[0])
                        BFS_visited_nodes += 1
                        previous_node_dictionary[nbr[0]] = current_node
                        if nbr[0] == global_node_count:
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
    def abbreviatedDijkstra() -> []:
        # Dijkstra variables
        global sumPath
        priorityQueue = []  # heap based on distance array variable
        sumPath = 1  # count includes starting node 1, count all node visits
        shortestPath = arr.array('i')  # unique node shortest path
        visitedNodes = set()  # set of visited nodes with unique nodes to prevent retracing steps
        distance = arr.array('i', [0, 0])  # map that stores all the distances from the source node
        heapq.heappush(priorityQueue, (0, 1))  # add starting node: always start at node 1 and distance 0
        visitedNodes.add(1)  # add starting node: always start at node 1
        ancestor = set()  # store node and ancestor
        origin = 1  # origin set to 1

        i = 2
        while i != (global_node_count + 1):
            distance.append(global_node_count)  # load each distance in initial map with INT_MAX
            i += 1

        while origin != global_node_count:
            for nbr in mazeGraph.adj[origin].items():  # step through neighbors of origin
                if nbr[0] not in visitedNodes:  # except for nodes already visited
                    u = origin  # get current node
                    v = nbr[0]  # neighbor
                    w = 1  # u->v the weight of the edge
                    if distance[v] > (distance[u] + w):
                        distance[v] = distance[u] + w
                        heapq.heappush(priorityQueue, (distance[v], v))
                        sumPath += 1  # increment sumPath
                        visitedNodes.add(v)
                        ancestor.add((v, origin))
            origin = priorityQueue[0][1]  # move origin to next item in heap
            heapq.heappop(priorityQueue)  # pop item off heap

        # creating shortest path vector (will be reverse order)
        origin = global_node_count  # start
        while origin != 1:
            # Find an element in list of tuples.
            for item in ancestor:
                if item[0] == origin:
                    origin = item[1]
                    shortestPath.append(item[0])
        shortestPath.append(origin)

        ascending_order_path = []
        x = len(shortestPath)
        for i in range(0, x):
            ascending_order_path.append(shortestPath.pop())

        return ascending_order_path

    # set the mood with some MUSIC! also loads sound effects
    solve_click = pygame.mixer.Sound("assets/click.wav")
    end_maze_sound = pygame.mixer.Sound("assets/Success.mp3")
    pygame.mixer.music.load('assets/Intro-Music.mp3')
    pygame.mixer.music.set_volume(0.5)
    pygame.mixer.music.play(-1)

    # UNCOMMENT LATER.

    # will execute all 3 algorithms on currently selected maze size (Dijkstra, BFS, DFS)
    # results output visually for smaller mazes, times only for 100k size
    def run_the_maze():
        global solved
        global mazeGraph
        global visited_cells
        global creation_stack
        global rows
        global GRAPH_SCALE_FACTOR
        visited_cells = []
        creation_stack = []
        rows = 0
        screen.fill(BLACK)
        menu.draw(screen)
        pygame.draw.rect(screen, GRAY, pygame.Rect(900, 400, 500, 500))
        mazeGraph = nx.Graph()
        pygame.display.update()
        define_rows()

        if global_node_count <= 1600:
            build_maze(global_node_count)
            create_the_maze()
            time.sleep(2)
            solve_the_maze()
            pygame.mixer.Sound.play(end_maze_sound)
            solved = True
        else:

            # here we will code the loading for bigger mazes.

            loading_text = font.render("Solving GIGANTIC Maze Number " + str(high_nodes_menu_choice), True,
                                       (255, 255, 255))
            loading_text2 = font.render("This might take a second. Please bear with us...", True, (255, 255, 255))
            loading_text3 = font.render("Dijkstra's algorithm is turning your CPU into a space heater", True, (255, 255,255))
            screen.blit(loading_text, (200, 350))
            screen.blit(loading_text2, (150, 400))
            screen.blit(loading_text3, (35, 450))
            pygame.display.update()
            if high_nodes_menu_choice == 1:
                mazeGraph = nx.read_gml("assets/graph100k_ONE.gml", destringizer=int)
            if high_nodes_menu_choice == 2:
                mazeGraph = nx.read_gml("assets/graph100k_TWO.gml", destringizer=int)
            if high_nodes_menu_choice == 3:
                mazeGraph = nx.read_gml("assets/graph100k_THREE.gml", destringizer=int)
            solve_the_maze_too_big()
            screen.fill(BLACK)
            pygame.mixer.Sound.play(end_maze_sound)
            loading_text = font.render("Solved!", True, (255, 255, 255))
            screen.blit(loading_text, (395, 450))

            solved = True

    # method to set node count of maze based on user input via menu
    def set_node_count(selected: Tuple, value: Any) -> None:
        global global_node_count
        global GRAPH_SCALE_FACTOR
        global high_nodes
        global SOLVE_SPEED
        if value == 1:
            global_node_count = 49
            btn.readonly = True
            btn.is_selectable = False
            slider.readonly = False
            slider.is_selectable = True
            slider2.readonly = False
            slider2.is_selectable = True
        if value == 2:
            global_node_count = 900
            btn.readonly = True
            btn.is_selectable = False
            slider.readonly = False
            slider.is_selectable = True
            slider2.readonly = False
            slider2.is_selectable = True
        if value == 3:
            global_node_count = 1600
            btn.readonly = True
            btn.is_selectable = False
            slider.readonly = False
            slider.is_selectable = True
            slider2.readonly = False
            slider2.is_selectable = True
        if value == 4:
            global_node_count = 100000
            SOLVE_SPEED = 0
            btn.readonly = False
            btn.is_selectable = True
            slider.readonly = True
            slider.is_selectable = False
            slider2.readonly = True
            slider2.is_selectable = False

    # will set creation maze delay for faster/slower creation depending on user preference, set via slider on menu
    def set_creation_speed(x):
        global CREATE_SPEED
        CREATE_SPEED = x

    # sets maze solution visualization speed faster/slower based on user input from slider
    def set_solve_speed(x):
        global SOLVE_SPEED
        SOLVE_SPEED = x

    # sets user choice of 100k size maze (select from 3 possibilities), sets variable high nodes menu choice equal to same
    def menu_choice(x, y):
        global high_nodes_menu_choice
        high_nodes_menu_choice = y

    menu = pygame_menu.Menu(
        height=400,
        width=500,
        mouse_motion_selection=True,
        position=(900, 0, False),
        theme=pygame_menu.themes.THEME_DARK,
        title='OPTIONS',
    )

    # construct pygame menu
    font_size_menu = 25
    menu.add.selector('Maze Node Count: ', [('49', 1), ('900', 2), ('1,600', 3), ('100,000', 4)],
                      onchange=set_node_count, font_size=font_size_menu)
    btn = menu.add.selector('Large Maze Choices: ', [('Graph 1', 1), ('Graph 2', 2), ('Graph 3', 3)],
                            onchange=menu_choice, font_size=font_size_menu)
    btn.readonly = True
    btn.is_selectable = False
    menu.add.label("----Speed Adjustment (Visuals)----", label_id="label_widget", font_size=font_size_menu)
    slider = menu.add.range_slider("Maze Creation Delay:", rangeslider_id="creation_speed_slider", default=.001,
                                   range_values=(0, 0.1), increment=10, onchange=set_creation_speed, font_size=font_size_menu)
    slider.readonly = False
    slider.is_selectable = True
    slider2 = menu.add.range_slider("Maze Solution Delay:", rangeslider_id="solve_speed_slider",
                                    default=.1, range_values=(0, 0.1), increment=10, onchange=set_solve_speed, font_size=font_size_menu)
    slider2.readonly = False
    slider2.is_selectable = True
    menu.add.button('Start Maze', run_the_maze, font_size=font_size_menu)
    menu.add.button('Back to Main Menu', main_menu, font_size=font_size_menu)

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

        if solved:
            dijkstra_text = font.render('Dijkstra: ', True, (0, 0, 0))
            dijkstra_nodes = font.render("Nodes Visited: " + str(sumPath), True, (0, 0, 0))
            dijkstra_solution_nodes = font.render("Nodes in Solution: " + str(len(maze_solution_dijkstra)), True,
                                                  (0, 0, 0))
            dijkstra_solve = font.render("Time to solve (ms): " + str(execution_time_dijkstra), True, (0, 0, 0))

            DFS_text = font.render('Depth First Search: ', True, (0, 0, 0))
            DFS_nodes = font.render("Nodes Visited: " + str(DFS_nodes_visited), True, (0, 0, 0))
            DFS_solution_nodes = font.render("Nodes in Solution: " + str(len(maze_solution_DFS)), True, (0, 0, 0))
            DFS_solve = font.render("Time to solve (ms): " + str(execution_time_DFS), True, (0, 0, 0))
            BFS_text = font.render('Breadth First Search: ', True, (0, 0, 0))

            BFS_text = font.render('Breadth First Search: ', True, (0, 0, 0))
            BFS_nodes = font.render("Nodes Visited: " + str(BFS_visited_nodes), True, (0, 0, 0))
            BFS_solution_nodes = font.render("Nodes in Solution: " + str(len(maze_solution_BFS)), True, (0, 0, 0))
            BFS_solve = font.render("Time to solve (ms): " + str(execution_time_BFS), True, (0, 0, 0))

            winner = font.render('Fastest Algorithm: ', True, (0, 0, 0))
            font_winner = font.render(winning_algo, True, (0, 0, 0))

            screen.blit(dijkstra_text, (900, 400))
            screen.blit(dijkstra_solve, (950, 430))
            screen.blit(dijkstra_nodes, (950, 460))
            screen.blit(dijkstra_solution_nodes, (950, 490))

            screen.blit(DFS_text, (900, 550))
            screen.blit(DFS_solve, (950, 580))
            screen.blit(DFS_nodes, (950, 610))
            screen.blit(DFS_solution_nodes, (950, 640))

            screen.blit(BFS_text, (900, 700))
            screen.blit(BFS_solve, (950, 730))
            screen.blit(BFS_nodes, (950, 760))
            screen.blit(BFS_solution_nodes, (950, 790))

            screen.blit(winner, (900, 840))
            screen.blit(font_winner, (1180, 840))

        for event in pygame.event.get():
            if event.type == pygame.locals.QUIT:
                pygame.quit()
                sys.exit()
            if event.type == pygame.KEYDOWN:
                if event.key == pygame.K_ESCAPE:
                    running = False

        pygame.display.update()


def options():
    screen = pygame.display.set_mode((WIDTH, HEIGHT))
    Background_options = pygame.image.load("assets/UF.png")
    while True:
        screen.fill((230, 230, 250))
        screen.blit(Background_options, (0, 0))
        OPTIONS_MOUSE_POS = pygame.mouse.get_pos()

        OPTIONS_TEXT = get_font(45).render("Created by:", True, "WHITE")
        OPTIONS_RECT = OPTIONS_TEXT.get_rect(center=(650, 100))

        Zak_TEXT = get_font(45).render("Zachary Schirm", True, "WHITE")
        Zak_RECT = OPTIONS_TEXT.get_rect(center=(650, 220))

        Aaron_TEXT = get_font(45).render("Aaron Hamburger", True, "WHITE")
        Aaron_RECT = OPTIONS_TEXT.get_rect(center=(650, 300))

        Serg_TEXT = get_font(45).render("Sergio Arcila", True, "WHITE")
        Serg_RECT = OPTIONS_TEXT.get_rect(center=(650, 380))

        UF_TEXT = get_font(45).render("UFL COP3530 FINAL PROJECT", True, "WHITE")
        UF_RECT = OPTIONS_TEXT.get_rect(center=(400, 600))

        screen.blit(OPTIONS_TEXT, OPTIONS_RECT)
        screen.blit(Aaron_TEXT, Aaron_RECT)
        screen.blit(Zak_TEXT, Zak_RECT)
        screen.blit(Serg_TEXT, Serg_RECT)
        screen.blit(Zak_TEXT, Zak_RECT)
        screen.blit(UF_TEXT, UF_RECT)

        OPTIONS_BACK = Button(image=None, pos=(700, 800),
                              text_input="BACK", font=get_font(75), base_color="Black", hovering_color="Green")

        OPTIONS_BACK.changeColor(OPTIONS_MOUSE_POS)
        OPTIONS_BACK.update(screen)

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit()
                sys.exit()
            if event.type == pygame.MOUSEBUTTONDOWN:
                if OPTIONS_BACK.checkForInput(OPTIONS_MOUSE_POS):
                    main_menu()

        pygame.display.update()


def drawOutline(x, y, string, col, size, window):
    font = pygame.font.Font("assets/font.ttf", size)
    text = font.render(string, True, col)
    textbox = text.get_rect()
    textbox.center = (x, y)
    window.blit(text, textbox)


def main_menu():
    pygame.mixer.music.load('assets/maze-music.wav')
    pygame.mixer.music.set_volume(0.8)
    pygame.mixer.music.play(-1)
    screen = pygame.display.set_mode((WIDTH, HEIGHT))
    pygame.display.set_caption("Mighty Maze Magicians Present: The Magical Maze Solver!")

    Background = pygame.image.load("assets/Maze.jpg")

    while True:
        screen.blit(Background, (0, 0))

        Mouse = pygame.mouse.get_pos()

        MENU_TEXT = get_font(60).render("THE MAGICAL MAZE SOLVER", True, "#b68f40")
        WELCOME_TEXT = get_font(60).render("WELCOME TO", True, "#b68f40")
        MENU_RECT = MENU_TEXT.get_rect(center=(700, 220))
        WELCOME_RECT = WELCOME_TEXT.get_rect(center=(700, 100))
        x = 700
        y = 220
        drawOutline(x + 3, y - 2, "THE MAGICAL MAZE SOLVER", BLACK, 60, screen)
        # top right
        drawOutline(x + 5, y - 4, "THE MAGICAL MAZE SOLVER", BLACK, 60, screen)

        y2 = 100
        drawOutline(x + 3, y2 - 2, "WELCOME TO", BLACK, 60, screen)
        # top right
        drawOutline(x + 5, y2 - 4, "WELCOME TO", BLACK, 60, screen)

        PLAY_BUTTON = Button(image=pygame.image.load("assets/Options Rect.png"), pos=(700, 500),
                             text_input="PLAY", font=get_font(60), base_color="#86f67d", hovering_color="White")
        OPTIONS_BUTTON = Button(image=pygame.image.load("assets/quit Rect.png"), pos=(200, 700),
                                text_input="CREDITS", font=get_font(49), base_color="#d7fcd4", hovering_color="White")
        QUIT_BUTTON = Button(image=pygame.image.load("assets/Quit Rect.png"), pos=(1200, 700),
                             text_input="QUIT", font=get_font(55), base_color="#e8351a", hovering_color="White")

        screen.blit(MENU_TEXT, MENU_RECT)
        screen.blit(WELCOME_TEXT, WELCOME_RECT)

        for button in [PLAY_BUTTON, OPTIONS_BUTTON, QUIT_BUTTON]:
            button.changeColor(Mouse)
            button.update(screen)

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit()
                sys.exit()
            if event.type == pygame.MOUSEBUTTONDOWN:
                if PLAY_BUTTON.checkForInput(Mouse):
                    theMainMaze()
                if OPTIONS_BUTTON.checkForInput(Mouse):
                    options()
                if QUIT_BUTTON.checkForInput(Mouse):
                    pygame.quit()
                    sys.exit()

        pygame.display.update()


main_menu()
theMainMaze()


# Attributions:
# Free sounds/music from zapsplat.com
# Royalty free images from pixabay.com
# 8.2 Dijkstra's Shortest Paths From Source Vertex to all Vertices
