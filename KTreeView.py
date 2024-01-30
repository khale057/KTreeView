# Tool to visualize cell hierarchies as a tree map
# Squarify treemap algorithm taken from: https://www.win.tue.nl/~vanwijk/stm.pdf
# Author: kha.le
import pygame, os, fileinput, random, math, pyperclip
import tkinter as tk
from tkinter import filedialog

pygame.init()

# initial settings
SCREEN_WIDTH = 1280
SCREEN_HEIGHT = 720
screen = pygame.display.set_mode((SCREEN_WIDTH, SCREEN_HEIGHT), pygame.RESIZABLE)
pygame.display.set_caption('KTreeView')
clock = pygame.time.Clock()
running = True

# global variables
encode_type = 'ISO-8859-1'
file_path = ''
topcell = ''
draw_instructions = []
cached_draw_instructions = {}
cached_leaf_counts = {}
tool_tip_text = ''
current_shown_hierarchy = ''
tree_root = None
progress_bar_current = 0
progress_bar_total = 99

# fonts
font_arial_11 = pygame.font.SysFont('Arial', 11)
font_arial_12 = pygame.font.SysFont('Arial', 12)
font_arial_20 = pygame.font.SysFont('Arial', 20)

# colors
GRADIENT_WHITE = (255, 255, 255)
GRADIENT_BLUE = (218, 228, 239)
BUTTON_COLOR = (253, 253, 253)
BUTTON_OUTLINE = (210, 210, 210)
BUTTON_COLOR_HOVER = (224, 238, 249)
BUTTON_OUTLINE_HOVER = (0, 120, 212)
CELL_OUTER_COLOR = (72, 72, 72)
CELL_OUTER_OUTLINE_COLOR = (64, 64, 64)
CELL_OUTER_OUTLINE_COLOR_HOVER = (176, 176, 176)
CELL_INNER_COLORS = ['tomato', 'turquoise', 'violetred', 'wheat', 'yellow', 'tan', 'steelblue', 'springgreen', 'sienna', 'slateblue']
TOOLTIP_COLOR = (249, 249, 249)
TOOLTIP_OUTLINE_COLOR = (180, 180, 180)
PROGRESS_BAR_EMPTY_COLOR = (230, 230, 230)
PROGRESS_BAR_FILL_COLOR = (18, 180, 47)
PROGRESS_BAR_OUTLINE_COLOR = (188, 188, 188)

# ========================================================
#    Tree Classes
# ========================================================

class RectFrame:
	__slots__ = ('x', 'y', 'width', 'height')

	def __init__(self, x, y, width, height):
		self.x = x
		self.y = y
		self.width = width
		self.height = height

class PositionRatio:
	"""
	Object to store position ratio information
	Used to compute the position/size of each cell in a relative format 
	(to be flexible for any frame size)
	
	Attributes:
	(All are floats between 0 and 1)
	- x: displacement from the left border
	- y: displacement from the top border
	- width: width
	- height: height
	
	Example:
	A cell with PositionRatio(0.2, 0.5, 0.4, 0.8) is in a frame
	It will be 0.2 of the frame's width away from the left
	It will be 0.5 of the frame's height away from the top
	Its width will be 0.4 of the frame's width
	Its height will be 0.8 of the frame's height
	"""
	__slots__ = ('x', 'y', 'width', 'height')

	def __init__(self, x, y, width, height):
		self.x = x
		self.y = y
		self.width = width
		self.height = height

	def __repr__(self):
		return '(' + ', '.join([str(item) for item in [self.x, self.y, self.width, self.height]]) + ')'

def adjust_rectangle_dimensions(width, height, new_area):
	"""
	Adjust the input width and height so they have the same aspect ratio, but produce the new area
	"""	
	aspect_ratio = width / height
	new_width = (new_area * aspect_ratio) ** 0.5
	new_height = new_width / aspect_ratio
	return new_width, new_height

class TreeNode:
	"""
	Data structure to store tree hierarchy
	
	Attributes:
	- name: name of the cell (str)
	- parent: reference to the parent TreeNode
	- children: dict of references to the children TreeNodes
	- ratios: a tuple of the format (displacement from left, displacement from top, width, height) where each item is between 0 and 1
			  these are "position ratios" that store the position/size of each cell in a relative format to be flexible for any frame size
	"""
	__slots__ = ('name', 'parent', 'children', 'ratio')
	
	def __init__(self, name, parent=None):
		self.name = name
		self.parent = parent		
		self.children = {}
		self.ratio = None
		
	def add_child(self, child_node):
		self.children[child_node.name] = child_node
	
	def get_size(self):
		"""
		Represents the units of space this cell would taken up within a frame
		Leaf nodes take up 1 unit of space
		Non-leaf nodes take up X units of space, where X is the size of their children combined
		"""
		return max(1, self.get_children_count())
	
	def get_children_count(self):
		count = len(self.children)
		for child in self.children.values():
			count += child.get_children_count()
		return count
	
	def get_full_path(self):		
		if self.parent == None: return ''
		
		full_path = ''
		if self.parent != None:
			full_path += self.parent.get_full_path() + '/' + self.name
		return full_path
	
	def get_leaf_count(self):
		global cached_leaf_counts
		
		if not self.children: return 1  
		if self.get_full_path() in cached_leaf_counts: return cached_leaf_counts[self.get_full_path()]
				
		leaf_count = 0
		for child in self.children.values():
			leaf_count += child.get_leaf_count()
			
		cached_leaf_counts[self.get_full_path()] = leaf_count
		return leaf_count
	
	def update_ratios(self, reference_width, reference_height):
		"""
		Recursively updates the position ratios for children
		Ratios are based off of the screen dimensions at the time of processing
		"""		
		children_to_update = [child for child in self.children.values()]
		children_to_update = sorted(children_to_update, key = lambda node : node.get_children_count()) # reading in decreasing order yields better results
		
		total_size_of_children = sum([node.get_size() for node in children_to_update])
		reference_width, reference_height = adjust_rectangle_dimensions(reference_width, reference_height, total_size_of_children)

		global_ratio_x = 0
		global_ratio_y = 0
		
		current_width = reference_width
		current_height = reference_height
		
		# begin square-based partitioning
		while len(children_to_update) > 0:
		
			is_wider = current_width > current_height
			partition_length = current_height if is_wider else current_width
			
			partition_buffer = []
			
			smallest_partition_block_aspect_ratio = 0
			
			# keep adding cells to partition buffer until smallest cell breaks ratio of 2
			while smallest_partition_block_aspect_ratio < 2 and len(children_to_update) > 0:
				partition_buffer.append(children_to_update.pop())
				
				partition_buffer_size = sum([node.get_size() for node in partition_buffer])
				smallest_partition_width = partition_buffer_size / partition_length
				smallest_partition_length = partition_length * partition_buffer[-1].get_size() / partition_buffer_size # last cell added will have smallest aspect ratio because list is read in decreasing order
				smallest_partition_block_aspect_ratio = smallest_partition_width / smallest_partition_length

			if len(partition_buffer) <= 0:
				print('[WARNING] Empty partition buffer found. Unable to draw remaining cells. There were ' + str(len(children_to_update)) + ' cells in queue.')
				children_to_update = []
				break
			
			if len(partition_buffer) != 1:
				# the last cell added ruined the aspect ratio, so add it back to the queue
				children_to_update.append(partition_buffer.pop()) 
		
			partition_buffer_total_area = sum([node.get_size() for node in partition_buffer])
			partition_width = partition_buffer_total_area / partition_length
			
			current_ratio_x = global_ratio_x
			current_ratio_y = global_ratio_y
						
			# start at one end of the partition, and keep processing until we reach end
			if is_wider:
				global_ratio_width = partition_width / reference_width
				
				for node in partition_buffer:
					current_ratio_height = node.get_size() / partition_buffer_total_area
					global_ratio_height = current_ratio_height * current_height / reference_height
					
					node.update_ratios(partition_width, partition_length * current_ratio_height) 
					node.ratio = PositionRatio(global_ratio_x, current_ratio_y, global_ratio_width, global_ratio_height)
					
					current_ratio_y += global_ratio_height
					
				global_ratio_x += global_ratio_width
				current_width -= partition_width					
			else:
				global_ratio_height = partition_width / reference_height
			
				for node in partition_buffer:
					current_ratio_width = node.get_size() / partition_buffer_total_area
					global_ratio_width = current_ratio_width * current_width / reference_width
					
					node.update_ratios(partition_length * current_ratio_width, partition_width)
					node.ratio = PositionRatio(current_ratio_x, global_ratio_y, global_ratio_width, global_ratio_height)
					
					current_ratio_x += global_ratio_width
					
				global_ratio_y += global_ratio_height
				current_height -= partition_width
					
	def generate_draw_instructions(self, rect_frame):
		"""
		Append instructions on how to draw the cell (and its children)
		to the global list of DrawInstruction(s)
		
		Arguments:
		- rect_frame: RectFrame object detailing the frame within to draw
		"""
		global draw_instructions, progress_bar_current

		if len(self.children) == 0:			
			draw_instructions.append(DrawInstruction(self.get_full_path(), pygame.Rect(rect_frame.x, rect_frame.y, rect_frame.width, rect_frame.height), random.choice(CELL_INNER_COLORS)))
			
			progress_bar_current += 1
			if progress_bar_current % 50 == 0: update_progress_bar('Drawing: ')
		else:
			draw_instructions.append(DrawInstruction(self.get_full_path(), pygame.Rect(rect_frame.x, rect_frame.y, rect_frame.width, rect_frame.height), CELL_OUTER_COLOR))
		
		if rect_frame.width <= 10*2 or rect_frame.height <= 20*2: # not enough space to draw children
			for child in self.children.values():
				progress_bar_current += child.get_leaf_count()
			return 
			
		for child in self.children.values():
			draw_region_width = rect_frame.width - 10
			draw_region_height = rect_frame.height - 20
			
			draw_x = rect_frame.x + 5 + draw_region_width * child.ratio.x
			draw_y = rect_frame.y + 15 + draw_region_height * child.ratio.y
			draw_width = draw_region_width * child.ratio.width
			draw_height = draw_region_height * child.ratio.height
			child.generate_draw_instructions(RectFrame(draw_x, draw_y, draw_width, draw_height))
		
	def print_tree(self, node, level=0):
		result = ' ' * level + node.name + ' ' + str(node.ratio) + '\n'
		for child in node.children.values():
			result += self.print_tree(child, level+1)
		return result
		
	def __str__(self):
		return self.print_tree(self)



# ========================================================
#    Hierarchy Building
# ========================================================
	
def display_hierarchy(node, hierarchy):
	"""
	Set the current shown hierarchy and display it
	
	Arguments:
	- hierarchy (str): a hierarchy text such as '/Chip/Tower/Transistor/'
	"""
	global current_shown_hierarchy, draw_instructions, cached_draw_instructions, progress_bar_current, progress_bar_total
	
	draw_instructions = []
	current_shown_hierarchy = hierarchy
	
	if hierarchy in cached_draw_instructions:
		draw_instructions = cached_draw_instructions[hierarchy]
		return

	current_node = node
	frame_margin = 10
	frame_top = 300
	initial_frame = RectFrame(frame_margin, frame_top, SCREEN_WIDTH - frame_margin*2, SCREEN_HEIGHT - frame_top - frame_margin)
	
	progress_bar_current = 0	
	
	parts = hierarchy.split('/')
	for index, part in enumerate(parts[1:]):
		part = part.rstrip('\n')
		
		if index == len(parts) - 2:
			progress_bar_total = current_node.children[part].get_leaf_count()
			current_node.children[part].generate_draw_instructions(initial_frame)
		current_node = current_node.children[part]
		
	cached_draw_instructions[current_shown_hierarchy] = draw_instructions

def add_hierarchy_to_tree(node, hierarchy):
	"""
	Adds a hierarchy to the root tree object
	
	Arguments:
	- hierarchy (str): a hierarchy text such as '/Chip/Tower/Transistor/'
	"""
	current_node = node
	
	parts = hierarchy.split('/')
	for part in parts[1:]:
		part = part.rstrip('\n')
		if part not in current_node.children:
			current_node.add_child(TreeNode(part, current_node))
		current_node = current_node.children[part]

def build_tree_from_text(file_path, encoding='ISO-8859-1'):
	"""
	Load a hierarchy text file and process it into a tree data structure
	
	Returns:
	- the root of the newly generated tree
	"""
	global progress_bar_current, progress_bar_total
	file_handler = open(file_path, 'r', encoding=encoding)
	
	progress_bar_total = sum([1 for line in file_handler])
	file_handler.seek(0)
	
	root = TreeNode('')
	current_node = root
	
	progress_bar_current = 0
	for line in file_handler:
		progress_bar_current += 1
		if not line.startswith('/'): continue # invalid hierarchy name
		add_hierarchy_to_tree(root, line)
		
		if progress_bar_current % 500 == 0: update_progress_bar('Processing: ')
		
	file_handler.close()
	
	return root

def get_topcell(file_path, encoding='ISO-8859-1'):
	"""
	Finds the topcell of the hierarchy; assumes that there is only one topcell
	"""
	topcell = ''
	file_handler = open(file_path, 'r', encoding=encoding)
	
	for line in file_handler:
		parts = line.split('/')
		if line.startswith('/') and len(parts) > 1 and parts[1] != '':
			topcell = '/'.join(parts[:2]).strip('\n')
			break
			
	file_handler.close()
	if not topcell: print('[WARNING] Topcell not found in hierarchy')
	return topcell

def load_hierarchy(file_path):	
	"""
	Loads a hierarchy text file
	This will update the topcell, build the tree, then display it
	"""
	global tree_root, topcell, cached_draw_instructions, current
		
	if os.path.exists(file_path):
		cached_draw_instructions = {}
		cached_leaf_counts = {}
		
		topcell = get_topcell(file_path)
		tree_root = build_tree_from_text(file_path)
		
		
		update_progress_bar('Updating ratios...', empty=True)
		tree_root.update_ratios(SCREEN_WIDTH, SCREEN_HEIGHT)
				
		display_hierarchy(tree_root, topcell)
		
def open_file_browser():
	"""
	Opens a file browser to select a hierarchy to open
	"""
	global file_path
	root = tk.Tk()
	root.withdraw() # hide main window
	
	retrieved_file_path = filedialog.askopenfilename()
	if retrieved_file_path != '':
		file_path = retrieved_file_path
		load_hierarchy(file_path)
	
	root.destroy() # close tkinter window
	


# ========================================================
#    Drawing Functions
# ========================================================
	
class DrawInstruction:
	__slots__ = ('name', 'rect_reference', 'color', 'display_name')

	def __init__(self, name, rect_reference, color):
		self.name = name
		self.rect_reference = rect_reference
		self.color = color
		self.display_name = name.split('/')[-1]
				
		if self.rect_reference.width < 40 or self.rect_reference.height < 15:
			self.display_name = ''
		else:			
			heuristic = self.rect_reference.width/6 
			while len(self.display_name) > heuristic and len(self.display_name) > 4:
				self.display_name = self.display_name.rstrip('.')
				self.display_name = self.display_name[:int(len(self.display_name)/2)]+'...'
	
def make_and_display_rect(surface, top, left, width, height, 
			  color=None, outline_color=None, text='', text_color='black', 
			  is_center=True, from_left=0, from_top=0, font=pygame.font.SysFont('Arial', 12),
			  mouse_pos=None, hover_color=None, hover_outline_color=None, outline_size=2, tip_text=None):
	"""
	Creates and returns a pygame Rect reference, along with displaying it
	"""
	global tool_tip_text
	rect_reference = pygame.Rect(top, left, width, height)
	
	if mouse_pos != None and rect_reference.collidepoint(mouse_pos):
		if hover_color != None: pygame.draw.rect(surface, hover_color, rect_reference)
		if hover_outline_color != None: pygame.draw.rect(surface, hover_outline_color, rect_reference, outline_size)
		
		if tip_text != None: tool_tip_text = tip_text
	else:
		if color != None: pygame.draw.rect(surface, color, rect_reference)
		if outline_color != None: pygame.draw.rect(surface, outline_color, rect_reference, outline_size) 
	
	if text != '':
		text_surface = font.render(text, True, text_color)
		if is_center:
			rect_surface = text_surface.get_rect(center = rect_reference.center)
		else:
			rect_surface = text_surface.get_rect(left = rect_reference.left + from_left, top = rect_reference.top + from_top)
		surface.blit(text_surface, rect_surface)
			
	return rect_reference
	
def draw_cell(surface, hover, rect, text, color):
	"""
	Draws the cell given information from the DrawInstruction
	
	To-do:
	- Better coloring system
	- Better logic; it is a bit hard-coded right now for testing purposes
	"""
	if color == CELL_OUTER_COLOR: # internal node ("folder")
		pygame.draw.rect(surface, color, rect)
		
		if hover: pygame.draw.rect(surface, CELL_OUTER_OUTLINE_COLOR_HOVER, rect, 2)
		else: pygame.draw.rect(surface, CELL_OUTER_OUTLINE_COLOR, rect, 2)

		text_surface = font_arial_11.render(text, True, 'white')
		rect_surface = text_surface.get_rect(top=rect.top+3, left=rect.left+3)
		surface.blit(text_surface, rect_surface)
		
	else:  # leaf node
		pygame.draw.rect(surface, color + '3', rect)
		
		if hover: pygame.draw.rect(surface, CELL_OUTER_OUTLINE_COLOR_HOVER, rect, 2)
		else: pygame.draw.rect(surface, color + '4', rect, 2)
		
def draw_gradient_background(surface, start_color, end_color):
	for y in range(SCREEN_HEIGHT):
		color = [start_color[i] + (end_color[i] - start_color[i]) * y / SCREEN_HEIGHT for i in range(3) ]
		pygame.draw.line(surface, color, (0, y), (SCREEN_WIDTH, y))

def update_progress_bar(text, empty=False):
	progress_bar_progress = progress_bar_current/progress_bar_total
	if empty: progress_bar_progress = 0
	
	progress_bar_background_ref = pygame.Rect(SCREEN_WIDTH-225, 25, 200, 25)
	progress_bar_ref = pygame.Rect(SCREEN_WIDTH-225, 25, 200*progress_bar_progress, 25)
	progress_bar_text_ref = pygame.Rect(SCREEN_WIDTH-225, 75, 200, 50)
	
	pygame.draw.rect(screen, PROGRESS_BAR_EMPTY_COLOR, progress_bar_background_ref)
	pygame.draw.rect(screen, PROGRESS_BAR_FILL_COLOR, progress_bar_ref)
	pygame.draw.rect(screen, PROGRESS_BAR_OUTLINE_COLOR, progress_bar_background_ref, 2)
	
	pygame.draw.rect(screen, 'white', progress_bar_text_ref)
	fraction_complete = str(progress_bar_current) + '/' + str(progress_bar_total)
	if empty: fraction_complete = ''
	text_surface = font_arial_12.render(text + fraction_complete, True, 'black')
	rect_surface = text_surface.get_rect(left=progress_bar_text_ref.left, top=progress_bar_text_ref.top)
	screen.blit(text_surface, progress_bar_text_ref)
	
	pygame.display.flip()



# ========================================================
#    Main Loop
# ========================================================

while running: 
	screen.fill('white')
	draw_gradient_background(screen, GRADIENT_WHITE, GRADIENT_BLUE)
	mouse_pos = pygame.mouse.get_pos()
	tool_tip_text = ''
	
	# top-left panel
	file_path_title_ref = make_and_display_rect(screen, 20, 15, 0, 0, text='File Path:', is_center=False, font=font_arial_20)
	file_path_ref = make_and_display_rect(screen, 110, 15, 0, 0, text=file_path if file_path else 'None', is_center=False, font=font_arial_20)
	
	select_ref = make_and_display_rect(screen, 20, 55, 0, 0, text='Select:', is_center=False, font=font_arial_20)
	open_button_ref = make_and_display_rect(screen, 88, 52, 45, 30, text='Open', is_center=True, font=font_arial_12, color=BUTTON_COLOR, outline_color=BUTTON_OUTLINE, hover_color=BUTTON_COLOR_HOVER, hover_outline_color=BUTTON_OUTLINE_HOVER, mouse_pos=mouse_pos)
	
	# tree-map bar
	if current_shown_hierarchy:
		current_hierarchy_ref = make_and_display_rect(screen, 12, 282, 200, 50, text='['+current_shown_hierarchy+']', is_center=False, font=font_arial_12)

		zoom_out_ref = make_and_display_rect(screen, SCREEN_WIDTH/2-25-3-14, 270, 25, 25, text='_', is_center=True, font=font_arial_12, color=BUTTON_COLOR, outline_color=BUTTON_OUTLINE, hover_color=BUTTON_COLOR_HOVER, hover_outline_color=BUTTON_OUTLINE_HOVER, mouse_pos=mouse_pos, tip_text='Zoom out Treemap')
		
		reset_tree_ref = make_and_display_rect(screen, SCREEN_WIDTH/2+3-14, 270, 25, 25, text='\\', is_center=True, font=font_arial_12, color=BUTTON_COLOR, outline_color=BUTTON_OUTLINE, hover_color=BUTTON_COLOR_HOVER, hover_outline_color=BUTTON_OUTLINE_HOVER, mouse_pos=mouse_pos, tip_text='Reset tree expansion')
		
		copy_shown_ref = make_and_display_rect(screen, SCREEN_WIDTH/2+31+3-14, 270, 25, 25, text='C', is_center=True, font=font_arial_12, color=BUTTON_COLOR, outline_color=BUTTON_OUTLINE, hover_color=BUTTON_COLOR_HOVER, hover_outline_color=BUTTON_OUTLINE_HOVER, mouse_pos=mouse_pos, tip_text='Copy current root to clipboard')
		
	# tree-map display
	for instruction in draw_instructions:
		hover = instruction.rect_reference.collidepoint(mouse_pos)
		draw_cell(screen, hover, instruction.rect_reference, instruction.display_name, instruction.color)
		if hover: tool_tip_text = instruction.name

	# tooltip
	if tool_tip_text != '':
		text_surface = font_arial_11.render(tool_tip_text, True, 'black')

		tooltip_display = pygame.Rect(min(mouse_pos[0]+15, SCREEN_WIDTH-text_surface.get_size()[0]-20), mouse_pos[1]-35, text_surface.get_size()[0]+12, 20)
		pygame.draw.rect(screen, TOOLTIP_COLOR, tooltip_display)
		pygame.draw.rect(screen, TOOLTIP_OUTLINE_COLOR, tooltip_display, 2)  # Outline
		rect_surface = text_surface.get_rect(left=tooltip_display.left+6, top = tooltip_display.top+3)
		screen.blit(text_surface, rect_surface)

	# poll for events
	for event in pygame.event.get():
		if event.type == pygame.QUIT:
			running = False
			
		if event.type == pygame.MOUSEBUTTONDOWN:
			
			if event.button == 1: # left mouse button

				# clicking a tree map region
				for instruction in reversed(draw_instructions):
					if instruction.rect_reference.collidepoint(event.pos) and instruction.color == CELL_OUTER_COLOR:
						display_hierarchy(tree_root, instruction.name)
						break
				
				# click the zoom out / reset expansion buttons
				if current_shown_hierarchy:
					if zoom_out_ref.collidepoint(event.pos):
						one_hierarchy_up = '/'.join(current_shown_hierarchy.split('/')[:-1])
						display_hierarchy(tree_root, one_hierarchy_up)
					elif reset_tree_ref.collidepoint(event.pos):
						display_hierarchy(tree_root, topcell)
					elif copy_shown_ref.collidepoint(event.pos):
						pyperclip.copy(current_shown_hierarchy)
										
				# clicking the open button
				if open_button_ref.collidepoint(event.pos):
					open_file_browser()
					
			elif event.button == 3: # right mouse button
				for instruction in reversed(draw_instructions):
					if instruction.rect_reference.collidepoint(event.pos):
						pyperclip.copy(instruction.name)
						print(instruction.name)
						break
			
		if event.type == pygame.VIDEORESIZE:
			SCREEN_WIDTH = event.w
			SCREEN_HEIGHT = event.h
			screen = pygame.display.set_mode((SCREEN_WIDTH, SCREEN_HEIGHT), pygame.RESIZABLE)
			
			cached_draw_instructions = {}
			display_hierarchy(tree_root, current_shown_hierarchy)
			
	pygame.display.flip()

pygame.quit()







