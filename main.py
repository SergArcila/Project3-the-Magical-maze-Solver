import pygame
import time
import random
import networkx as nx
import math

# create a new graph using networkx package
mazeGraph = nx.Graph()

# set up pygame window
WIDTH = 1200
HEIGHT = 900
FPS = 30
GRAPH_X_OFFSET = 0
GRAPH_Y_OFFSET = 0
GRAPH_SCALE_FACTOR = 1

# Define colours
WHITE = (255, 255, 255)
GREEN = (0, 255, 0,)
BLUE = (0, 0, 255)
YELLOW = (255, 255, 0)
BLACK = (0, 0, 0)
RED = (255, 0, 0)

# initialise Pygame
pygame.init()
pygame.mixer.init()
screen = pygame.display.set_mode((WIDTH, HEIGHT))
pygame.display.set_caption("Mighty Maze Magicians Present: The Magical Maze Solver!")
clock = pygame.time.Clock()

# setup maze TODO: these need to be dynamic/user input based on maze size
visited_cells = []
creation_stack = []
global_node_count = 1600 # user input this value
rows = math.sqrt(global_node_count)  # the global node count needs to be perfect square to make cubic maze
rows = int(rows)  # wants to give float value - need int - casting to same


# method to construct maze grid of squares
def build_maze(node_count):

    # add node_number (user input) of nodes to mazeGraph graph (networkx)
    for i in range(1, node_count + 1):
        mazeGraph.add_node(i)

    # draw background color of maze
    pygame.draw.rect(screen, BLUE, pygame.Rect(GRAPH_X_OFFSET + 20, GRAPH_Y_OFFSET + 20, 20*rows, 20*rows))

    # draw all individual cells (Rects), walls will overlap but will be drawn over during maze creation
    for j in range(0, rows):
        for k in range(0, rows):
            pygame.draw.rect(screen, WHITE, pygame.Rect((20 + GRAPH_X_OFFSET + j * 20), (20 + GRAPH_Y_OFFSET + k * 20), 20, 20), width=1)

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
    pygame.draw.rect(screen, BLUE, pygame.Rect(x_pos*20 + 1 + GRAPH_X_OFFSET, y_pos*20 + 1 + GRAPH_Y_OFFSET, 18, 38))
    pygame.display.update()


# clear wall rightward
def move_right(node_number):
    if node_number % rows == 0:
        x_pos = rows
        y_pos = int(node_number / (rows + 1))
    else:
        x_pos = int(node_number % rows)
        y_pos = int(node_number / rows)
    pygame.draw.rect(screen, BLUE, pygame.Rect(x_pos*20 + 1 + GRAPH_X_OFFSET, y_pos*20 + 21 + GRAPH_Y_OFFSET, 38, 18))
    pygame.display.update()


# clear wall leftward
def move_left(node_number):
    if node_number % rows == 0:
        x_pos = rows
        y_pos = int(node_number / (rows + 1))
    else:
        x_pos = int(node_number % rows)
        y_pos = int(node_number / rows)
    pygame.draw.rect(screen, BLUE, pygame.Rect(x_pos*20 - 19 + GRAPH_X_OFFSET, y_pos*20 + 21 + GRAPH_Y_OFFSET, 38, 18))
    pygame.display.update()


# clear wall downward
def move_down(node_number):
    if node_number % rows == 0:
        x_pos = rows
        y_pos = int(node_number / (rows + 1))
    else:
        x_pos = int(node_number % rows)
        y_pos = int(node_number / rows)
    pygame.draw.rect(screen, BLUE, pygame.Rect(x_pos * 20 + 1 + GRAPH_X_OFFSET, y_pos * 20 + 21 + GRAPH_Y_OFFSET, 18, 38))
    pygame.display.update()


# color individual cell (for showing maze construction/tracking)
def color_one_cell(node_number):
    if node_number % rows == 0:
        x_pos = rows
        y_pos = int(node_number / (rows + 1))
    else:
        x_pos = int(node_number % rows)
        y_pos = int(node_number / rows)
    pygame.draw.rect(screen, YELLOW, pygame.Rect(x_pos * 20 + 1 + GRAPH_X_OFFSET, y_pos * 20 + 21 + GRAPH_Y_OFFSET, 18, 18))
    pygame.display.update()


# will color beginning cell of maze GREEN
def color_beginning(node_number):
    if node_number % rows == 0:
        x_pos = rows
        y_pos = int(node_number / (rows + 1))
    else:
        x_pos = int(node_number % rows)
        y_pos = int(node_number / rows)
    pygame.draw.rect(screen, GREEN, pygame.Rect(x_pos * 20 + 1 + GRAPH_X_OFFSET, y_pos * 20 + 21 + GRAPH_Y_OFFSET, 18, 18))
    pygame.display.update()


# will color end cell of maze RED
def color_end(node_number):
    if node_number % rows == 0:
        x_pos = rows
        y_pos = int(node_number / (rows + 1))
    else:
        x_pos = int(node_number % rows)
        y_pos = int(node_number / rows)
    pygame.draw.rect(screen, RED, pygame.Rect(x_pos * 20 + 1 + GRAPH_X_OFFSET, y_pos * 20 + 21 + GRAPH_Y_OFFSET, 18, 18))
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
    pygame.draw.rect(screen, BLUE, pygame.Rect(x_pos * 20 + 1 + GRAPH_X_OFFSET, y_pos * 20 + 21 + GRAPH_Y_OFFSET, 18, 18))
    pygame.display.update()


# solution cell that shows small box in center to mark path/solution
def show_solution_cell(node_number):
    if node_number % rows == 0:
        x_pos = rows
        y_pos = int(node_number / (rows + 1))
    else:
        x_pos = int(node_number % rows)
        y_pos = int(node_number / rows)
    pygame.draw.rect(screen, WHITE, pygame.Rect(x_pos * 20 + 8 + GRAPH_X_OFFSET, y_pos * 20 + 28 + GRAPH_Y_OFFSET, 3, 3))
    pygame.display.update()


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
        time.sleep(.001)
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
                time.sleep(.01)  # pause for effect
                uncolor_one_cell(current_cell)  # erase backtracking visual
                visited_cells.append(current_cell)
                creation_stack.append(current_cell)

            elif random_cell == "left":
                move_left(current_cell)
                mazeGraph.add_edge(current_cell, current_cell - 1)
                current_cell = current_cell - 1
                color_one_cell(current_cell)  # visual to show backtracking
                time.sleep(.01)  # pause for effect
                uncolor_one_cell(current_cell)  # erase backtracking visual
                visited_cells.append(current_cell)
                creation_stack.append(current_cell)

            elif random_cell == "up":
                move_up(current_cell)
                mazeGraph.add_edge(current_cell, current_cell - rows)
                current_cell = current_cell - rows
                color_one_cell(current_cell)  # visual to show backtracking
                time.sleep(.01)  # pause for effect
                uncolor_one_cell(current_cell)  # erase backtracking visual
                visited_cells.append(current_cell)
                creation_stack.append(current_cell)

            elif random_cell == "down":
                move_down(current_cell)
                mazeGraph.add_edge(current_cell, current_cell + rows)
                current_cell = current_cell + rows
                color_one_cell(current_cell)  # visual to show backtracking
                time.sleep(.01)  # pause for effect
                uncolor_one_cell(current_cell)  # erase backtracking visual
                visited_cells.append(current_cell)
                creation_stack.append(current_cell)

        else:
            current_cell = creation_stack.pop()
            color_end(current_cell)  # visual to show backtracking
            time.sleep(.01)  # pause for effect
            uncolor_one_cell(current_cell)  # erase backtracking visual

    # Mark beginning of maze green and end red
    color_beginning(1)
    color_end(global_node_count)


# using Networkx build in libraries to solve maze w/ Dijkstra and Bellman-Ford
# report time to execute for each
# display solution visually and as a vector in console
def solve_the_maze():
    maze_solution = []
    maze_solution_2 = []
    start_time = time.time()
    maze_solution = nx.shortest_path(mazeGraph, 1, global_node_count, weight=None, method='dijkstra')
    end_time = time.time()
    execution_time = end_time - start_time
    print('Dijkstras algorithm took:', execution_time, 'seconds to execute')
    start_time = time.time()
    maze_solution_2 = nx.shortest_path(mazeGraph, 1, global_node_count, weight=None, method='bellman-ford')
    end_time = time.time()
    execution_time = end_time - start_time
    print('Bellman-Ford algorithm took:', execution_time, 'seconds to execute')
    print('The solution to the maze in vector of nodes form:')
    print(maze_solution)
    display_maze_solution(maze_solution)


# method to show the solution to the maze visually
def display_maze_solution(maze_solution):
    for i in maze_solution:
        show_solution_cell(i)
        pygame.mixer.Sound.play(solve_click)
        time.sleep(0.05)


# build maze grid, create the maze (carve out), sleep for 2 seconds for dramatic effect, solve the maze
solve_click = pygame.mixer.Sound("536108__eminyildirim__ui-click.wav")
end_maze_sound = pygame.mixer.Sound("zapsplat_multimedia_game_sound_childrens_soft_twinkling_finish_end_tone_005_60683.mp3")
pygame.mixer.music.load('music_zapsplat_aiming_high.mp3')
pygame.mixer.music.play(-1)
build_maze(global_node_count)
create_the_maze()
time.sleep(2)
solve_the_maze()
pygame.mixer.Sound.play(end_maze_sound)

# pygame loop
running = True
while running:
    clock.tick(FPS)
    for event in pygame.event.get():
        if event.type == pygame.QUIT:
            running = False
