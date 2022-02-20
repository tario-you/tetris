import time
from itertools import chain
from pynput import keyboard
import threading
import random
import math

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
held_piece = []
previous_held = []
score = 0

# ticks per second
tps = 4

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
        if empty == bottom_pixels:
            for i in range(len(self.locations)):
                self.locations[i] = (self.locations[i][0]+1,self.locations[i][1])
        else:
            self.moving = False

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
        grid[l[0]][l[1]] = f'{c.red}#{c.endc}'

def spawn(piece): # spawn a tetromino class, match its color, append to tetrominos
    t_p = tetromino(piece, get_color_from_shape(piece), get_identity_from_shape(piece))
    tetrominos.append(t_p)

def get_identity_from_shape(shape):
    if shape == box: return 'o'
    elif shape == line: return 'i'
    elif shape == li: return 'j'
    elif shape == lr: return 'l'
    elif shape == zi: return 's'
    elif shape == zr: return 'z'
    elif shape == tp: return 't'

def get_color_from_shape(shape):
    if shape == box: return c.yellow
    elif shape == line: return c.cyan
    elif shape == li: return c.blue
    elif shape == lr: return c.white
    elif shape == zi: return c.green
    elif shape == zr: return c.red
    elif shape == tp: return c.purple

def population_control(): # all not moving pieces die
    global dead_locations
    while True:
        for t in tetrominos:
            if not t.moving:
                for location in t.locations:
                    dead_locations.append(location)
                tetrominos.remove(t)

def display_grid(): # displays game grid
    cls = lambda: print('\n' * 100) #sp.call('clear', shell=True) #os.system('clear')
    display = ''
    for row in grid:
        for e in row:
            display += str(e) + ' '
        display += '\n'
    display += f'score: {score}\n'
    print(display)

    with open('/Users/tarioyou/Desktop/Files/Code/dumb2/tetris/logs.txt','a') as f:
        for row in grid:
            for e in row:
                if e != 0 and e != '-' and e != '|': f.write("1 ")
                else: f.write(f'{e} ')
            f.write("\n")
        f.write("\n")

'''def print_and_log(string):
    print(string)
    with open('/Users/tarioyou/Desktop/Files/Code/dumb2/tetris/logs.txt','a') as f:
        f.write(str(string))'''

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
        for t in tetrominos:
            t.step()
            t.refresh_board()
        render_dead()
        clean_grid()
        display_grid()
        time.sleep(1/tps)
        
def clear_lines(): # when a line is full, delete line, move everything else down
    global dead_locations
    global score
    n = len(grid)
    
    # finding each role that is full
    full_rows = []
    zero_count = []
    for i in range(n-1):
        row = grid[i] 
        if row.count(0)==0 and i != n-1:
            full_rows.append(i)
        zero_count.append(row.count(0))

    if len(full_rows) >= 1:
        # finding changes that should be done to each row
        changes = [] 
        for i in range(n-1):
            if i in full_rows: 
                changes.append(-1)
            else:
                larger_val = 0
                for fr in full_rows:
                    if i < fr: 
                        larger_val += 1
                changes.append(larger_val)

        # comitting changes onto a new_dead_locations
        new_dead_locations = []
        for dl in dead_locations:
            dly = dl[0]
            dlx = dl[1]
            if changes[dly] != -1:
                new_dead_locations.append((dly+changes[dly],dlx))

        # comitting changes to dead_locations
        dead_locations = new_dead_locations

        # scoring
        score += math.ceil(math.pow(len(full_rows),0.8))

def hold_current_piece():
    global held_piece
    global previous_held
    active_piece = tetrominos[0].shape
    # make sure no repeated holding / changing
    if held_piece == []:
        held_piece = active_piece
        tetrominos[0].locations = []
        tetrominos[0].moving = False
    elif active_piece != previous_held:
        temp = held_piece
        previous_held = held_piece
        held_piece = active_piece
        active_piece = temp
        # spawn active_piece
        tetrominos[0].shape = active_piece
        # spawn locations = what they would be if you spawned a new active_piece
        tetrominos[0].locations = tetromino(active_piece, f'{c.red}', get_identity_from_shape(active_piece)).locations
        tetrominos[0].identity = get_identity_from_shape(active_piece)
        tetrominos[0].color = get_color_from_shape(active_piece)
    
def auto_spawn(): # spawn new pieces when there are no live pieces
    def add_next_piece():
        if True: 
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
                    time.sleep(0.01)
            if key == keyboard.Key.up:
                for t in tetrominos:
                    if t.moving: t.rotate('cw')
            if key == keyboard.Key.esc:
                quit()
        clean_grid()
        display_grid() 
        #return
    def on_release(key):
        return
        
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