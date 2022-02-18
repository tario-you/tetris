import time
from itertools import chain
from pynput import keyboard
import threading
import random
import os

# presets for rotation
i = [[0,0,0,0],
     [1,1,1,1],
     [0,0,0,0],
     [0,0,0,0]]
o = [[1,1],
     [1,1]]
j = [[1,0,0],
     [1,1,1],
     [0,0,0]]
l = [[0,0,1],
     [1,1,1],
     [0,0,0]]
s = [[0,1,1],
     [1,1,0],
     [0,0,0]]
z = [[1,1,0],
     [0,1,1],
     [0,0,0]]
t = [[0,1,0],
     [1,1,1],
     [0,0,0]]
shapes = [i,o,j,l,s,z,t]
block_rotation_states = {} 
shape_names = ['i','o','j','l','s','z','t']

global spawn_count
spawn_count = 0    
clear = lambda: os.system('clear')

# creating all the rotation states for all the blocks
for i in range(len(shapes)):
    name = shape_names[i]
    block_rotation_states[name] = [(shapes[i])] # state 0

    # state 1-3
    for i in range(3):
        block_rotation_states[name].append(list(zip(*block_rotation_states[name][-1]))[::-1])
    temp2 = block_rotation_states[name][1] # a copy of state 2
    block_rotation_states[name][1] = block_rotation_states[name][3].copy() # state 2 -> state 4
    block_rotation_states[name][3] = temp2 # state 4 -> state 2

# actual presets for each of the tetris pieces
box = [[0,1,1,0],
       [0,1,1,0]] # o
line = [[0,0,0,0], 
        [1,1,1,1]] # i
li = [[1,0,0,0],
      [1,1,1,0]] # j
lr = [[0,0,1,0],
      [1,1,1,0]] # l
zi = [[0,1,1,0],
      [1,1,0,0]] # s
zr = [[1,1,0,0],
      [0,1,1,0]] # z
tp = [[0,1,0,0],
     [1,1,1,0]] # t
pieces = [box,line,li,lr,zi,zr,tp]
next_pieces = []

# board dimensions and board setup
height = 23
width = 10
grid = [['|']+[0 for i in range (width)]+['|'] for i in range(height)]
grid.append(['-' for i in range(width+2)])

# all tetris pieces stored in here 
tetrominos = []
dead_locations = []
debug = False

# ticks per second
tps = 2

# only available colors in the metaverse that i bothered finding 
class c:
    black = '\x1b[31;1m'
    red = '\x1b[31;1m'
    green = '\x1b[32;1m'
    yellow = '\x1b[33;1m'
    blue = '\x1b[34;1m'
    purple = '\x1b[35;1m'
    cyan = '\x1b[36;1m'
    white = '\x1b[37;1m'
    endc = '\033[0m'

def column(matrix, i): # get a column from a 2d array
    return [row[i] for row in matrix]

class tetromino: # tetris blocks class
    def __init__(self,shape_arr,color, identity_):
        self.shape = shape_arr
        self.n = list(chain.from_iterable(shape_arr)).count(1)
        self.locations = []
        self.previous_locations = []
        self.color = color
        self.moving = True
        self.rotation_state = 0
        # finding the block's game grid location
        for y in range (2): 
            for x in range (4):
                if shape_arr[y][x] != 0:
                    self.locations.append((y,x+4))
        # self identity
        self.identity = identity_

    def step(self): # move down one if below is empty
        self.previous_locations = self.locations.copy()
        bottom_pixels = 0
        empty = 0
        below_location_content = {}
        for location in self.locations: 
            y = location[0] # real y, x locations
            x = location[1]
            below_location_content[(y+1,x)] = [(y,x),grid[y+1][x]]
            if (y+1,x) not in self.locations: # locations that are outside of the shape and in the grid
                bottom_pixels += 1
                if grid[y+1][x] == 0:
                    empty += 1
        if debug: 
            print(below_location_content)
            print(self.moving)
        if empty == bottom_pixels:
            for i in range(len(self.locations)):
                self.locations[i] = (self.locations[i][0]+1,self.locations[i][1])
        else:
            self.moving = False
        with open('/Users/tarioyou/Desktop/Files/Code/dumb2/tetris/logs.txt','a') as f:
            f.write(str(below_location_content))
            f.write('\n')

    def move_left(self): # if left is clear, move left
        if self.moving:
            self.previous_locations = self.locations.copy()
            meet_r = 0
            for location in self.locations:
                y = location[0]
                x = location[1]
                if (y,x-1) in self.locations or grid[y][x-1] == 0:
                    meet_r += 1
            if meet_r == self.n:
                for i in range(len(self.locations)):
                    self.locations[i] = (self.locations[i][0],self.locations[i][1]-1)

    def move_right(self): # if right is clear, move right
        if self.moving:
            self.previous_locations = self.locations.copy()
            meet_r = 0
            for location in self.locations:
                y = location[0]
                x = location[1]
                if (y,x+1) in self.locations or grid[y][x+1] == 0:
                    meet_r += 1
            if meet_r == self.n:
                for i in range(len(self.locations)):
                    self.locations[i] = (self.locations[i][0],self.locations[i][1]+1)

    def rotate(self, rotation_direction:str): # rotate if cells of next rotation state are free cw/ccw
        if debug: print(f'{c.red}rotate called{c.endc}')
        if self.moving:
            current_state = self.rotation_state
            if rotation_direction == 'cw':
                next_state = self.rotation_state + 1
                if next_state == 4:
                    next_state = 0
            elif rotation_direction == 'ccw':
                next_state = self.rotation_state - 1
                if next_state == -1:
                    next_state = 3
            if debug: print(f'{current_state=}\t{next_state=}')
            current_position = block_rotation_states[self.identity][current_state] # real 3x3 grid
            next_position = block_rotation_states[self.identity][next_state]
            # self.locations : [(x,y) * 4]
            # translation required = rotation_pos_x + something = real_x, rotation_pos_y + something = real_y
            xs = []; ys = []
            for l in self.locations:
                xs.append(l[1])
                ys.append(l[0])
            xmin = min(xs); ymin = min(ys)
            new_locations = []
            for l in self.locations:
                x=l[1]
                y=l[0]
                new_locations.append((y-ymin,x-xmin)) # list of current piece position adjusted to a 3x3 grid
            # see if current piece positions were correctly casted onto a 3x3 grid, else correct
            if new_locations != current_position: # might turn to while
                if new_locations[0] == current_position[1] and new_locations[1] == current_position[2]:
                    ymin -= 1
                elif column(new_locations,0) == column(current_position,1) and column(new_locations,1) == column(current_position, 2):
                    xmin -= 1
                elif new_locations[0][0] == current_position[1][1] and new_locations[0][1] == current_position[1][2] and new_locations[1][0] == current_position[2][1] and new_locations[1][1] == current_position[2][2]:
                    ymin -= 1
                    xmin -= 1
                new_locations = []
                for l in self.locations:
                    x=l[1]
                    y=l[0]
                    new_locations.append((y-ymin,x-xmin))

            #print(f'{new_locations=}\n{current_position=}\n{next_position=}\n{self.locations=}')

            # now the things matches up and ymin and xmin are accurate
            required_empty = 0
            new_rotation_location_on_grid = []
            for y in range(len(next_position)):
                for x in range(len(next_position)):
                    if next_position[y][x] == 1:
                        new_rotation_location_on_grid.append((y+ymin, x+xmin))
                        required_empty += 1

            actual_empty = 0
            for location in new_rotation_location_on_grid:
                if grid[location[0]][location[1]] == 0:
                    actual_empty += 1
                elif location in self.locations:
                    actual_empty += 1

            #print(f'{required_empty=}\n{actual_empty=}\n{new_rotation_location_on_grid=}')

            if actual_empty == required_empty:
                for i in range(len(self.locations)):
                    self.locations[i] = (new_rotation_location_on_grid[i][0],new_rotation_location_on_grid[i][1])
                # update rotation state
                if rotation_direction == 'cw':
                    self.rotation_state += 1
                    if self.rotation_state == 4:
                        self.rotation_state = 0
                elif rotation_direction == 'ccw':
                    self.rotation_state -= 1
                    if self.rotation_state == -1:
                        self.rotation_state = 3

    def delete_block_piece(self, coordinate): # for when line clearing ocurrs
        self.locations.remove(coordinate)

    def hard_drop(self): # hard drop
        while self.moving:
            self.step()

    def refresh_board(self): # tell game grid the block's new position
        if self.moving:
            for p in self.previous_locations:
                grid[p[0]][p[1]] = 0
        for n in self.locations:
            grid[n[0]][n[1]] = f'{self.color}#{c.endc}'

def render_dead(): # cant set global variable need to set dead_locations to new_dead_locations
    for l in dead_locations:
        grid[l[0]][l[1]] = f'{c.black}#{c.endc}'

def spawn(piece): # spawn a tetromino class, match its color, append to tetrominos
    if piece == box: 
        color = c.yellow
        identity = 'o'
    elif piece == line: 
        color = c.cyan
        identity = 'i'
    elif piece == li: 
        color = c.blue
        identity = 'j'
    elif piece == lr: 
        color = c.white
        identity = 'l'
    elif piece == zi: 
        color = c.green
        identity = 's'
    elif piece == zr: 
        color = c.red
        identity = 'z'
    elif piece == tp: 
        color = c.purple
        identity = 't'
    else: print(f'{c.red}invalid block{c.endc}')
    t_p = tetromino(piece, color, identity)
    tetrominos.append(t_p)

def population_control(): # all not moving pieces die
    global dead_locations
    while True:
        for t in tetrominos:
            if not t.moving:
                for location in t.locations:
                    dead_locations.append(location)
                tetrominos.remove(t)

def display_grid(): # displays game grid
    clear()
    print()
    for row in grid:
        for i, e in enumerate(row):
            print(e,end=' ')
        print()
    print()

    with open('/Users/tarioyou/Desktop/Files/Code/dumb2/tetris/logs.txt','a') as f:
        for row in grid:
            for e in row:
                if e != 0 and e != '-' and e != '|': f.write("1 ")
                else: f.write(f'{e} ')
            f.write("\n")
        f.write("\n")

def print_and_log(string):
    print(string)
    with open('/Users/tarioyou/Desktop/Files/Code/dumb2/tetris/logs.txt','a') as f:
        f.write(str(string))

def clean_grid(): # clear spaces where there are no blocks
    global dead_locations
    tetromino_locations = []
    for t in tetrominos:
        for location in t.locations: 
            tetromino_locations.append(location)
    clear_lines()
    for y in range(height):
        for x in range(width+2):
            if (y,x) not in tetromino_locations and y != height and x != 0 and x != width+1 and (y,x) not in dead_locations:
                grid[y][x] = 0

def tick(): # tick all blocks down one 
    while True:
        if debug: print(tetrominos)
        for t in tetrominos:
            t.step()
            t.refresh_board()
        render_dead()
        clean_grid()
        display_grid()
        time.sleep(1/tps)
        
def clear_lines(): # when a line is full, delete line, move everything else down
    global dead_locations
    # remove everything on the cleared out line
    n = len(grid)
    for y in range(len(grid)):
        ny = -y-1 # counting down backwards: -1, -2, -3...
        ay =  n-y-1 # countindg backwards positively: 19, 18, 17...
        if grid[ny].count(0) == 0: # a row is full / no zero's left
            print(f'{ny} is full')
            if ny != -1:
                global dead_locations
                new_dead_locations = []
                for i, dl in enumerate(dead_locations):
                    dly = dl[0]
                    dlx = dl[1]
                    if dl[0] < ay: # if dead piece is above the full row
                        new_dead_locations.append((dly+1,dlx)) # move dead piece down one
                    elif dly != ay:
                        new_dead_locations.append((dly,dlx))
                print_and_log(f'old {dead_locations}\nnew {new_dead_locations}')
                dead_locations = new_dead_locations

def hold_current_piece(piece):
    held_piece = piece

def auto_spawn(): # spawn new pieces when there are no live pieces
    def add_next_piece():
        random.shuffle(pieces)
        for e in pieces:
            next_pieces.append(e)

    while True:
        if len(tetrominos) == 0:
            if len(next_pieces) < 6:
                add_next_piece()
            spawn(next_pieces[0])
            del next_pieces[0]

def read(): # read user input
    def on_press(key):
        #print('{0} pressed'.format(key))   
        return
    def on_release(key):
        #print('{0} released'.format(key))
        if 'char' in dir(key):
            if key.char == 'c':
                hold_current_piece()
        else:
            if key == keyboard.Key.left:
                for t in tetrominos:
                    if t.moving: t.move_left()
            if key == keyboard.Key.right:
                for t in tetrominos:
                    if t.moving: t.move_right()
            if key == keyboard.Key.space:
                for t in tetrominos:
                    if t.moving: t.hard_drop()
            if key == keyboard.Key.up:
                for t in tetrominos:
                    if t.moving: t.rotate('cw')
            if key == keyboard.Key.esc:
                quit()
        clean_grid()
        display_grid()
    # Collect events until released
    with keyboard.Listener(on_press =on_press, 
        on_release=on_release) as listener:
        listener.join()

if __name__ == "__main__":
    # threading for near parallel execution
    
    # thread creation
    population_control_thread = threading.Thread(target=population_control)
    tick_thread = threading.Thread(target=tick)
    read_thread = threading.Thread(target=read)  
    auto_spawn_thread = threading.Thread(target=auto_spawn)
    

    # thread initiation
    population_control_thread.start()
    auto_spawn_thread.start()
    tick_thread.start()
    read_thread.start() 

    # joining thread to center process
    population_control_thread.join()
    auto_spawn_thread.join()
    tick_thread.join()
    read_thread.join()