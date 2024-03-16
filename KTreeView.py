# Tool to visualize cell hierarchies as a tree map
# Squarify treemap algorithm: https://www.win.tue.nl/~vanwijk/stm.pdf
# Author: kha.le
import pygame, os, math, pyperclip, colorsys
import tkinter as tk
from collections import namedtuple, deque
from datetime import datetime
from tkinter import filedialog

pygame.init()
pygame.display.set_caption('KTreeView')

# ========================================================
#    Classes
# ========================================================

RectFrame = namedtuple('RectFrame', ['x', 'y', 'width', 'height'])
PositionRatio = namedtuple('PositionRatio', ['x', 'y', 'width', 'height'])
RatioStep = namedtuple('RatioStep', ['node', 'reference_width', 'reference_height'])
DrawStep = namedtuple('DrawStep', ['node', 'rect_frame'])
CellRect = namedtuple('CellRect', ['full_path', 'rect'])

class KTreeViewRunner:
	"""
	Main runner for KTreeView
	"""
	
	def __init__(self):
		
		# initial settings
		self.screen_width = 1280
		self.screen_height = 720
		self.screen = pygame.display.set_mode((self.screen_width, self.screen_height), pygame.RESIZABLE)
		self.encoding = 'ISO-8859-1'
		self.clock = pygame.time.Clock()
		self.mouse_pos = pygame.mouse.get_pos()
		self.last_mouse_pos = (0, 0)
		
		# tree region dimensions
		self.frame_margin = 10
		self.frame_top = 300
		self.initial_frame = RectFrame(
			self.frame_margin, 
			self.frame_top, 
			self.screen_width - self.frame_margin*2, 
			self.screen_height - self.frame_top - self.frame_margin
		)
		
		# hierarchy
		self.file_path = ''
		self.top_cell = ''
		self.current_shown_hierarchy = ''
		self.tree_root = None
		
		# surfaces
		self.surfaces = {}
		for category in ['background', 'buttons', 'tree', 'text', 'hover', 'tooltip']:
			self.surfaces[category] = pygame.Surface((self.screen_width,self.screen_height), pygame.SRCALPHA)
			self.surfaces[category] = self.surfaces[category].convert_alpha()
		self.update_canvas = True

		# caching
		self.text_cache = {}
		self.text_cache['black'] = {}
		self.text_cache['white'] = {}
		self.text_cache['tooltip'] = {}
		self.text_cache['tooltip']['(Right-click to copy path)'] = pygame.font.SysFont('Arial', 11).render('(Right-click to copy path)', True, 'black')
		self.text_cache['tooltip'][''] = pygame.font.SysFont('Arial', 11).render('', True, 'black')
		self.tree_cache = {}
		
		# recursion queues
		self.ratio_queue = deque()
		self.draw_queue = deque()
		
		# collision
		self.cell_rects = {} # check for cursor hover
		self.spatial_partition_size = 5
		for row in range(self.spatial_partition_size):
			for col in range(self.spatial_partition_size):
				self.cell_rects[row*self.spatial_partition_size+col] = []
		self.mouse_down = None # check for LMB click
		self.cell_hover = {} # stores the last hover state of each cell
		self.buttons_list = []
		
		# tooltip
		self.tooltip = ''
		self.last_tooltip = ''
		self.tooltip_display_width = 0
		self.tooltip_line_count = 0
		
		# progress bar
		self.progress_current = 0
		self.progress_total = 99
		
		# colors
		self.colors = {}
		
		self.colors['gradient'] = {}
		self.colors['gradient']['white'] = (255, 255, 255)
		self.colors['gradient']['blue'] = (218, 228, 239)
		
		self.colors['button'] = {}
		self.colors['button']['color'] = (253, 253, 253)
		self.colors['button']['outline'] = (210, 210, 210)
		
		self.colors['button_hover'] = {}
		self.colors['button_hover']['color'] = (224, 238, 249)
		self.colors['button_hover']['outline'] = (0, 120, 212)
		
		self.colors['leaf_node'] = {}
		self.colors['leaf_node']['color'] = (45, 45, 45)
		self.colors['leaf_node']['outline'] = (10, 10, 10)
		
		self.colors['tooltip'] = {}
		self.colors['tooltip']['color'] = (249, 249, 249)
		self.colors['tooltip']['outline'] = (180, 180, 180)
		
		self.colors['progress_bar'] = {}
		self.colors['progress_bar']['empty'] = (230, 230, 230)
		self.colors['progress_bar']['fill'] = (18, 180, 47)
		self.colors['progress_bar']['outline'] = (188, 188, 188)
		
		self.colors['cell_outline'] = (176, 176, 176)
		
		# button references
		self.file_title_button = self.Button(
			'[file-title]',
			pygame.Rect(20, 15, 0, 0),
			self,
			text='File Path:', 
			is_center=False, 
			font_size=20
		)
		
		self.file_button = self.Button(
			'[file-path]',
			pygame.Rect(110, 15, 0, 0),
			self,
			text='None', 
			is_center=False, 
			font_size=20
		)
		
		self.open_title_button = self.Button(
			'[open-title]',
			pygame.Rect(20, 55, 0, 0),
			self,
			text='Select:', 
			is_center=False, 
			font_size=20
		)

		self.open_button = self.Button(
			'[open-button]',
			pygame.Rect(88, 52, 45, 30),
			self,
			text='Open',
			button_color=self.colors['button']['color'], 
			button_outline=self.colors['button']['outline'], 
			button_hover_color=self.colors['button_hover']['color'], 
			button_hover_outline=self.colors['button_hover']['outline'],
			is_center=True, 
			font_size=13
		)
		
		self.zoom_out_button = self.Button(
			'[zoom-out]',
			pygame.Rect(self.screen_width/2-42, 250, 25, 25),
			self,
			text='_',
			button_color=self.colors['button']['color'], 
			button_outline=self.colors['button']['outline'], 
			button_hover_color=self.colors['button_hover']['color'], 
			button_hover_outline=self.colors['button_hover']['outline'],
			is_center=True, 
			font_size=12,
			tip_text='Zoom out Treemap'
		)
		
		self.reset_tree_button = self.Button(
			'[reset-tree]',
			pygame.Rect(self.screen_width/2-11, 250, 25, 25),
			self,
			text='\\',
			button_color=self.colors['button']['color'], 
			button_outline=self.colors['button']['outline'], 
			button_hover_color=self.colors['button_hover']['color'], 
			button_hover_outline=self.colors['button_hover']['outline'],
			is_center=True, 
			font_size=12,
			tip_text='Reset tree expansion'
		)
		
		self.copy_shown_button = self.Button(
			'[copy-shown]',
			pygame.Rect(self.screen_width/2+20, 250, 25, 25),
			self,
			text='C',
			button_color=self.colors['button']['color'], 
			button_outline=self.colors['button']['outline'], 
			button_hover_color=self.colors['button_hover']['color'], 
			button_hover_outline=self.colors['button_hover']['outline'],
			is_center=True, 
			font_size=12,
			tip_text='Copy current hierarchy to clipboard'
		)
		
	# ==================================
	#    Tree Class
	# ==================================
	
	class TreeNode:
		"""
		Data structure to store tree hierarchy
		
		Attributes:
		- name: name of the cell (str)
		- parent: reference to the parent TreeNode
		- children: dict of references to the children TreeNodes
		- ratio: PositionRatio object (namedtuple)
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
		
		def get_full_path(self):		
			if self.parent == None: return ''
			
			full_path = ''
			if self.parent != None:
				full_path += self.parent.get_full_path() + '/' + self.name
			return full_path
			
		def get_children_count(self):
			count = len(self.children)
			for child in self.children.values():
				count += child.get_children_count()
			return count
		
		def get_leaf_count(self):			
			if not self.children: return 1  
					
			leaf_count = 0
			for child in self.children.values():
				leaf_count += child.get_leaf_count()
				
			return leaf_count
		
		def print_tree(self, node, level=0):
			result = ' ' * level + node.name + ' ' + str(node.ratio) + '\n'
			for child in node.children.values():
				result += self.print_tree(child, level+1)
			return result
			
		def __str__(self):
			return self.print_tree(self)
	
	# ==================================
	#    Drawing Nodes
	# ==================================
			
	def hsv_to_rgb(self, hue, sat, val):
		"""
		Same as colorsys's hsv_to_rgb(), but in (255, 255, 255) format instead of (1, 1, 1)
		"""
		return tuple(round(item * 255) for item in colorsys.hsv_to_rgb(hue, sat, val))
	
	def get_hue(self, node):
		"""
		Returns the hue, generated from a hash of the path twice descended from currently shown hierarchy
		The motivation is for each sub-block in the currently shown hierarchy to have a distinct color
		
		Example:
			If the currently shown hierarchy is "/A/B/", then
			"/A/B/C/" and "/A/B/C/D" and "/A/B/C/D/E" will have the same color, but
			"/A/B/Z/" should have a different color
		"""
		full_path = node.get_full_path()
		path_descended_twice = '/'.join(full_path.split('/')[:self.current_shown_hierarchy.count('/')+2])
		hashed_path = hash(path_descended_twice)
		hue = (hashed_path % 255) / 255
		return hue

	def get_sat(self, node):
		"""
		Returns saturation, determined via the node's depth
		"""
		depth = node.get_full_path().count('/')
		sat = depth - self.current_shown_hierarchy.count('/')
		sat = 0.05 + sat / 16 # start at 0.05 saturation, and increment by 1/16 per depth
		return sat
	
	def get_color(self, node):
		"""
		Returns color for current node
		"""
		hue = self.get_hue(node)
		sat = self.get_sat(node)
		val = 1
		return self.hsv_to_rgb(hue, sat, val)
	
	def get_display_name(self, full_path, frame_width, frame_height):
		"""
		Returns the cell name, shortened if too long to display
		"""
		if frame_width < 40 or frame_height < 15:
			return '' # not enough space to display a name
		
		cell_name = full_path.split('/')[-1]
		heuristic = max(frame_width/6, 4)
		while len(cell_name) > heuristic:
			cell_name = cell_name.rstrip('.')
			cell_name = cell_name[:int(len(cell_name)/2)] + '...'
			
		return cell_name
	
	def draw_node_name(self, name, color, rect_frame):
		"""
		Draws the name of a node
		"""
		display_name = self.get_display_name(name, rect_frame.width, rect_frame.height)
			
		if display_name not in self.text_cache[color]:
			self.text_cache[color][display_name] = pygame.font.SysFont('Arial', 12).render(display_name, True, color)
			
		text_surface = self.text_cache[color][display_name]
		rect_surface = text_surface.get_rect(left=rect_frame.x+3, top=rect_frame.y+3)
		self.tree_cache[self.current_shown_hierarchy]['text'].blit(text_surface, rect_surface)
	
	def draw_node(self, node, rect_frame):
		"""
		Draws the node to the screen
		Also: Partitions the draw space into a grid and adds that node to that grid-space's collision check 
		When checking for collisions, it will first check which grid-space it is in to reduce the amount of collision checks
		"""
		current_cell_rectangle = CellRect(node.get_full_path(), pygame.Rect(rect_frame.x, rect_frame.y, rect_frame.width, rect_frame.height))

		# spatial partitioning
		for row in range(self.spatial_partition_size):
			for col in range(self.spatial_partition_size):
				quadrant = RectFrame(
					self.initial_frame.x+col*self.initial_frame.width/self.spatial_partition_size, 
					self.initial_frame.y+row*self.initial_frame.height/self.spatial_partition_size, 
					self.initial_frame.width/self.spatial_partition_size, 
					self.initial_frame.height/self.spatial_partition_size
				)
				if self.rectangle_collision(quadrant, rect_frame):
					self.tree_cache[self.current_shown_hierarchy]['rects'][row*self.spatial_partition_size+col].append(current_cell_rectangle)
		
		# draw
		if len(node.children) == 0:		
			pygame.draw.rect(self.tree_cache[self.current_shown_hierarchy]['surface'], self.colors['leaf_node']['color'], current_cell_rectangle.rect)
			pygame.draw.rect(self.tree_cache[self.current_shown_hierarchy]['surface'], self.colors['leaf_node']['outline'], current_cell_rectangle.rect, 2)
			
			self.draw_node_name(node.get_full_path(), 'white', rect_frame)
			
			self.progress_bar_current += 1
			if self.progress_bar_current % 50 == 0: self.update_progress_bar('Drawing: ')
		else:
			color = self.get_color(node)
			pygame.draw.rect(self.tree_cache[self.current_shown_hierarchy]['surface'], color, current_cell_rectangle.rect)			
			pygame.draw.rect(self.tree_cache[self.current_shown_hierarchy]['surface'], color, current_cell_rectangle.rect, 2)
			
			self.draw_node_name(node.get_full_path(), 'black', rect_frame)
		
		if rect_frame.width <= 10*2 or rect_frame.height <= 20*2: # not enough space to draw children
			for child in node.children.values():
				self.progress_bar_current += child.get_leaf_count()
			return 
		
		# draw the children (by adding to draw queue)
		for child in node.children.values():
			draw_region_width = rect_frame.width - 10
			draw_region_height = rect_frame.height - 20
			
			draw_x = rect_frame.x + 5 + draw_region_width * child.ratio.x
			draw_y = rect_frame.y + 15 + draw_region_height * child.ratio.y
			draw_width = draw_region_width * child.ratio.width
			draw_height = draw_region_height * child.ratio.height
			
			self.draw_queue.append(DrawStep(child, RectFrame(draw_x, draw_y, draw_width, draw_height)))
			
	def rectangle_collision(self, rect_a, rect_b):
		"""
		Return whether two rectangles collide or not
		"""
		return rect_a.x < rect_b.x + rect_b.width and rect_a.x + rect_a.width > rect_b.x and \
				rect_a.y < rect_b.y + rect_b.height and rect_a.y + rect_a.height > rect_b.y 
	
	# ==================================
	#    Updating Ratios
	# ==================================
	
	def adjust_rectangle_dimensions(self, width, height, new_area):
		"""
		Adjust the input width and height so they have the same aspect ratio, but produce the new area
		"""	
		aspect_ratio = width / height
		new_width = (new_area * aspect_ratio) ** 0.5
		new_height = new_width / aspect_ratio
		return new_width, new_height
	
	def update_ratio(self, node, reference_width, reference_height):
		"""
		Recursively updates the position ratios for children
		Ratios are based off of the screen dimensions at the time of processing					
		"""		
		children_to_update = [child for child in node.children.values()]
		children_to_update.sort(key = lambda cell : cell.get_children_count()) # reading in decreasing order yields better results
		
		total_size_of_children = sum([cell.get_size() for cell in children_to_update])
		reference_width, reference_height = self.adjust_rectangle_dimensions(reference_width, reference_height, total_size_of_children)

		global_ratio_x, global_ratio_y = 0, 0
		current_width, current_height = reference_width, reference_height
		
		# begin square-based partitioning
		while len(children_to_update) > 0:
		
			is_wider = current_width > current_height
			partition_length = current_height if is_wider else current_width
			
			partition_buffer = []
			
			smallest_partition_block_aspect_ratio = 0
			
			# keep adding cells to partition buffer until smallest cell breaks ratio of 2
			while smallest_partition_block_aspect_ratio < 2 and len(children_to_update) > 0:
				partition_buffer.append(children_to_update.pop())
				
				partition_buffer_size = sum([cell.get_size() for cell in partition_buffer])
				smallest_partition_width = partition_buffer_size / partition_length
				smallest_partition_length = partition_length * partition_buffer[-1].get_size() / partition_buffer_size # last cell added will have smallest aspect ratio because list is read in decreasing order
				smallest_partition_block_aspect_ratio = smallest_partition_width / smallest_partition_length

			if len(partition_buffer) <= 0:
				print('[WARNING] Empty partition buffer found. Unable to draw remaining cells. There were ' + str(len(children_to_update)) + ' cells left in queue.')
				children_to_update = []
				break
			
			if len(partition_buffer) != 1:
				# the last cell added ruined the aspect ratio, so add it back to the queue
				children_to_update.append(partition_buffer.pop()) 
		
			partition_buffer_total_area = sum([cell.get_size() for cell in partition_buffer])
			partition_width = partition_buffer_total_area / partition_length
			
			current_ratio_x, current_ratio_y = global_ratio_x, global_ratio_y
						
			# start at one end of the partition, and keep processing until we reach end
			if is_wider:
				global_ratio_width = partition_width / reference_width
				
				for cell in partition_buffer:
					current_ratio_height = cell.get_size() / partition_buffer_total_area
					global_ratio_height = current_ratio_height * current_height / reference_height
					
					self.ratio_queue.append(RatioStep(cell, partition_width, partition_length * current_ratio_height))
					cell.ratio = PositionRatio(global_ratio_x, current_ratio_y, global_ratio_width, global_ratio_height)
					
					current_ratio_y += global_ratio_height
					
				global_ratio_x += global_ratio_width
				current_width -= partition_width					
			else:
				global_ratio_height = partition_width / reference_height
			
				for cell in partition_buffer:
					current_ratio_width = cell.get_size() / partition_buffer_total_area
					global_ratio_width = current_ratio_width * current_width / reference_width
					
					self.ratio_queue.append(RatioStep(cell, partition_length * current_ratio_width, partition_width))
					cell.ratio = PositionRatio(current_ratio_x, global_ratio_y, global_ratio_width, global_ratio_height)
					
					current_ratio_x += global_ratio_width
					
				global_ratio_y += global_ratio_height
				current_height -= partition_width
	
	# ==================================
	#    Hierarchy Loading
	# ==================================
	
	def display_hierarchy(self, node, hierarchy):
		"""
		Set the current shown hierarchy and display it
		
		Arguments:
		- hierarchy (str): a hierarchy text such as '/Chip/Tower/Transistor/'
		"""
	
		self.cell_hover = {}
		self.current_shown_hierarchy = hierarchy
		if self.current_shown_hierarchy in self.tree_cache:
			self.surfaces['tree'] = self.tree_cache[self.current_shown_hierarchy]['surface']
			self.surfaces['text'] = self.tree_cache[self.current_shown_hierarchy]['text']
			self.cell_rects = self.tree_cache[self.current_shown_hierarchy]['rects']
			return
		
		# cache setup
		self.tree_cache[self.current_shown_hierarchy] = {}
		self.tree_cache[self.current_shown_hierarchy]['surface'] = pygame.Surface((self.screen_width,self.screen_height), pygame.SRCALPHA)
		self.tree_cache[self.current_shown_hierarchy]['surface'] = self.tree_cache[self.current_shown_hierarchy]['surface'].convert_alpha()
		self.tree_cache[self.current_shown_hierarchy]['text'] = pygame.Surface((self.screen_width,self.screen_height), pygame.SRCALPHA)
		self.tree_cache[self.current_shown_hierarchy]['text'] = self.tree_cache[self.current_shown_hierarchy]['text'].convert_alpha()
		self.tree_cache[self.current_shown_hierarchy]['rects'] = {}
		for row in range(self.spatial_partition_size):
			for col in range(self.spatial_partition_size):
				self.tree_cache[self.current_shown_hierarchy]['rects'][row*self.spatial_partition_size+col] = []	
		
		current_node = node		
		self.progress_bar_current = 0	
		
		# set current node to hierarchy
		parts = hierarchy.split('/')
		for part in parts[1:]:
			if part in current_node.children.keys():
				current_node = current_node.children[part]
				continue
			break
		
		self.progress_bar_total = current_node.get_leaf_count()
		self.draw_queue.append(DrawStep(current_node, self.initial_frame))
		
		while len(self.draw_queue) > 0:
			step = self.draw_queue.popleft()
			self.draw_node(step.node, step.rect_frame)
		
		self.surfaces['tree'] = self.tree_cache[self.current_shown_hierarchy]['surface']
		self.surfaces['text'] = self.tree_cache[self.current_shown_hierarchy]['text']
		self.cell_rects = self.tree_cache[self.current_shown_hierarchy]['rects']
		
	def add_hierarchy_to_tree(self, node, hierarchy):
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
				current_node.add_child(self.TreeNode(part, current_node))
			current_node = current_node.children[part]

	def build_tree_from_text(self, file_path):
		"""
		Load hierarchy text file and process it into a tree data structure
		
		Returns: Root of newly generated tree
		"""
		file_handler = open(file_path, 'r', encoding=self.encoding)
		
		self.progress_bar_total = sum([1 for line in file_handler])
		file_handler.seek(0)
		
		root = self.TreeNode('')
		current_node = root
		
		self.progress_bar_current = 0
		for line in file_handler:
			self.progress_bar_current += 1
			if not line.startswith('/'): continue # invalid hierarchy name
			self.add_hierarchy_to_tree(root, line)
			
			if self.progress_bar_current % 500 == 0: self.update_progress_bar('Processing: ')
			
		file_handler.close()
		
		return root
		
	def get_top_cell(self, file_path):
		"""
		Finds the topcell of the hierarchy; assumes that there is only one topcell
		"""
		top_cell = ''
		file_handler = open(file_path, 'r', encoding=self.encoding)
		
		for line in file_handler:
			parts = line.split('/')
			if line.startswith('/') and len(parts) > 1 and parts[1] != '':
				top_cell = '/'.join(parts[:2]).strip('\n')
				break
				
		file_handler.close()
		
		if not top_cell: print('[WARNING] Top cell not found in hierarchy')
		else: print('[Info] Top cell found: ' + str(top_cell))
		
		return top_cell

	def load_hierarchy(self, file_path):	
		"""
		Loads a hierarchy text file
		This will update the topcell, build the tree, then display it
		"""
		self.buttons_list = [self.open_button]
		
		if os.path.exists(file_path):
		
			self.top_cell = self.get_top_cell(file_path)
			self.tree_root = self.build_tree_from_text(file_path)
			
			self.update_progress_bar('Updating ratios...', empty=True)
			self.ratio_queue.append(RatioStep(self.tree_root, self.screen_width, self.screen_height))
		
			while len(self.ratio_queue) > 0:
				step = self.ratio_queue.popleft()
				self.update_ratio(step.node, step.reference_width, step.reference_height)
			
			self.tree_cache = {}
			self.display_hierarchy(self.tree_root, self.top_cell)
			
			for tree_button in [self.zoom_out_button, self.reset_tree_button, self.copy_shown_button]:
				self.buttons_list.append(tree_button)
			
			self.redraw_buttons()
			
	def open_file_browser(self):
		"""
		Opens a file browser to select a hierarchy to open
		"""
		root = tk.Tk()
		root.withdraw() # hide main window
		
		retrieved_file_path = filedialog.askopenfilename()
		if retrieved_file_path != '':
			self.file_path = retrieved_file_path
			self.file_button.text = self.file_path			
						
			self.load_hierarchy(self.file_path)
			
			self.update_background() # display new file path
			self.update_canvas = True
					
		root.destroy() # close tkinter window
	
	# ==================================
	#    Pygame Interface
	# ==================================
	
	class Button:
		"""
		Object to store button properties and reference
		"""
		__slots__ = (
			'name', 'reference', 'parent', 'text', 'text_color', 
			'button_color', 'button_outline', 'button_hover_color', 
			'button_hover_outline', 'outline_size', 'is_center', 
			'from_left', 'from_top', 'font', 'tip_text', 'last_hover'
		)
		
		def __init__(
			self, name, reference, parent,
			text = '',
			text_color = 'black', 
			button_color = None, 
			button_outline = None, 
			button_hover_color = None,
			button_hover_outline = None,
			outline_size = 2,
			is_center = True,
			from_left = 0,
			from_top = 0,
			font_family = 'Arial',
			font_size = 12,
			tip_text = ''
		):
			self.name = name
			self.reference = reference
			self.parent = parent
			
			self.text = text
			self.text_color = text_color
			
			self.button_color = button_color
			self.button_outline = button_outline
			self.button_hover_color = button_hover_color
			self.button_hover_outline = button_hover_outline
			
			self.outline_size = outline_size
			
			self.is_center =  is_center
			self.from_left = from_left
			self.from_top = from_top
			
			self.font = pygame.font.SysFont(font_family, font_size)
			self.tip_text = tip_text
			
			self.last_hover = False
				
		def draw(self, surface, hover=False):
			"""
			Draw button to surface
			"""
			if hover:
				if self.button_hover_color != None: pygame.draw.rect(surface, self.button_hover_color, self.reference)
				if self.button_hover_outline != None: pygame.draw.rect(surface, self.button_hover_outline, self.reference, self.outline_size)
				
				if self.tip_text != None: self.parent.tooltip = self.tip_text
			else:
				if self.button_color != None: pygame.draw.rect(surface, self.button_color, self.reference)
				if self.button_outline != None: pygame.draw.rect(surface, self.button_outline, self.reference, self.outline_size) 
										
			if self.text != '':
				text_surface = self.font.render(self.text, True, self.text_color)
				if self.is_center:
					rect_surface = text_surface.get_rect(center = self.reference.center)
				else:
					rect_surface = text_surface.get_rect(left = self.reference.left + self.from_left, top = self.reference.top + self.from_top)
					
				surface.blit(text_surface, rect_surface)
		
	def draw_gradient(self, surface, start_color, end_color):
		"""
		Draw gradient background
		"""
		for row in range(self.screen_height):
			color = [start_color[index] + (end_color[index] - start_color[index]) * row / self.screen_height for index in range(3) ] # RGB
			pygame.draw.line(surface, color, (0, row), (self.screen_width, row))
	
	def update_progress_bar(self, text, empty=False):
		"""
		Updates the progress bar display
		"""
		progress = self.progress_bar_current/self.progress_bar_total
		if empty: progress = 0
		
		bar_background	= pygame.Rect(self.screen_width-225, 25, 200, 25)
		bar				= pygame.Rect(self.screen_width-225, 25, 200*progress, 25)
		bar_text		= pygame.Rect(self.screen_width-225, 75, 200, 50)
				
		pygame.draw.rect(self.screen, self.colors['progress_bar']['empty'], bar_background)
		pygame.draw.rect(self.screen, self.colors['progress_bar']['fill'], bar)
		pygame.draw.rect(self.screen, self.colors['progress_bar']['outline'], bar_background, 2)		
		pygame.draw.rect(self.screen, 'white', bar_text)
		
		fraction_complete = str(self.progress_bar_current) + '/' + str(self.progress_bar_total)
		if empty: fraction_complete = ''
		
		text_surface =  pygame.font.SysFont('Arial', 12).render(text + fraction_complete, True, 'black')
		blit_reference = self.screen.blit(text_surface, bar_text)
		
		pygame.display.update([bar_background, bar, bar_text, blit_reference])
	
	def update_background(self):
		"""
		Update background surface for: resized window / new file path loaded
		"""
		self.draw_gradient(self.surfaces['background'], self.colors['gradient']['white'], self.colors['gradient']['blue'])		
		self.file_title_button.draw(self.surfaces['background'], hover=False)
		self.file_button.draw(self.surfaces['background'], hover=False)
		self.open_title_button.draw(self.surfaces['background'], hover=False)		
	
	def redraw_buttons(self):
		"""
		Updates the button displays
		"""
		self.zoom_out_button.reference = pygame.Rect(self.screen_width/2-42, 250, 25, 25)
		self.reset_tree_button.reference = pygame.Rect(self.screen_width/2-11, 250, 25, 25)
		self.copy_shown_button.reference = pygame.Rect(self.screen_width/2+20, 250, 25, 25)
		
		for button in self.buttons_list:
			button.draw(self.surfaces['buttons'], hover=False)
			
	def redraw_canvas(self):
		"""
		Update the canvas by blitting the subsurfaces to the main surface
		"""	
		#print('[Flip] ' + str(datetime.now()))
		
		for category in ['background', 'buttons', 'tree', 'text', 'hover']:
			self.screen.blit(self.surfaces[category], (0,0))
			
		tooltip_x = min(self.mouse_pos[0]+15, self.screen_width-self.tooltip_display_width-20)
		tooltip_y = self.mouse_pos[1]-22-13*self.tooltip_line_count
		self.screen.blit(self.surfaces['tooltip'], (tooltip_x,tooltip_y))
			
		pygame.display.flip()
	
	def event_polling(self):
		"""
		Poll for events to handle input, such as mouse-clicks
		"""
		for event in pygame.event.get():
		
			# exit
			if event.type == pygame.QUIT: 
				pygame.quit()
				raise SystemExit
			
			# mouse button
			if event.type == pygame.MOUSEBUTTONDOWN: 
								
				if event.button == 1: # LMB				
					# clicking a tree map region
					if self.mouse_down != None and self.mouse_down.rect.collidepoint(event.pos):
						self.display_hierarchy(self.tree_root, self.mouse_down.full_path)
						self.mouse_down = None
							
					# click the zoom out / reset expansion buttons
					if self.current_shown_hierarchy:						
						if self.zoom_out_button.reference.collidepoint(event.pos) and self.top_cell != self.current_shown_hierarchy:
							one_hierarchy_above = '/'.join(self.current_shown_hierarchy.split('/')[:-1])
							self.display_hierarchy(self.tree_root, one_hierarchy_above)
						elif self.reset_tree_button.reference.collidepoint(event.pos):
							self.display_hierarchy(self.tree_root, self.top_cell)
						elif self.copy_shown_button.reference.collidepoint(event.pos):
							pyperclip.copy(self.current_shown_hierarchy)
							
					# clicking the open button
					if self.open_button.reference.collidepoint(event.pos):
						self.open_file_browser()
				
				elif event.button == 3: # RMB
					if self.mouse_down != None and self.mouse_down.rect.collidepoint(event.pos):
						pyperclip.copy(self.mouse_down.full_path)
						print(self.mouse_down.full_path)
							
			# resizing window
			if event.type == pygame.VIDEORESIZE: 
				self.screen_width = event.w
				self.screen_height = event.h
				screen = pygame.display.set_mode((self.screen_width, self.screen_height), pygame.RESIZABLE)
				
				self.initial_frame = RectFrame(
					self.frame_margin, 
					self.frame_top, 
					self.screen_width - self.frame_margin*2, 
					self.screen_height - self.frame_top - self.frame_margin
				)
				
				for category in ['background', 'buttons', 'tree', 'text', 'hover', 'tooltip']:
					self.surfaces[category] = pygame.Surface((self.screen_width,self.screen_height), pygame.SRCALPHA)
					self.surfaces[category] = self.surfaces[category].convert_alpha()
				
				self.update_background()
				self.redraw_buttons()
				self.tree_cache = {}
				self.display_hierarchy(self.tree_root, self.current_shown_hierarchy) # re-display
				
	def tree_collision_check(self):
		"""
		Check if you are hovering over the tree cells
		"""
		self.surfaces['hover'].fill(pygame.Color(0, 0, 0, 0))
		mouse_x_offset = self.mouse_pos[0] - self.initial_frame.x
		mouse_y_offset = self.mouse_pos[1] - self.initial_frame.y
		
		within_frame = mouse_x_offset > 0 and mouse_y_offset > 0 and mouse_x_offset < self.initial_frame.width and mouse_y_offset < self.initial_frame.height
						
		if within_frame != self.cell_hover.get('last_within_frame', -1):
			self.update_canvas = True
						
		if within_frame:
			
			col = math.floor(mouse_x_offset / self.initial_frame.width * self.spatial_partition_size)
			row = math.floor(mouse_y_offset / self.initial_frame.height * self.spatial_partition_size)
			
			for cell_rect in self.cell_rects[row*self.spatial_partition_size + col]:
					
				hover = cell_rect.rect.collidepoint(self.mouse_pos)
				
				if hover != self.cell_hover.get(cell_rect.full_path, -1):
					self.update_canvas = True					
				self.cell_hover[cell_rect.full_path] = hover
				
				if hover: 
					pygame.draw.rect(self.surfaces['hover'], self.colors['cell_outline'], cell_rect.rect, 2)
					self.tooltip = cell_rect.full_path
					self.mouse_down = cell_rect
				
		self.cell_hover['last_within_frame'] = within_frame

	def draw_tooltip(self):
		"""
		Display tooltip message from hovering on something
		"""
		
		if self.tooltip == '':
			self.surfaces['tooltip'].fill(pygame.Color(0, 0, 0, 0))
			self.last_tooltip = self.tooltip
			return
			
		if self.tooltip != self.last_tooltip:
			self.surfaces['tooltip'].fill(pygame.Color(0, 0, 0, 0))
			text_surfaces = []
					
			# cell paths
			if '/' in self.tooltip:
				text_surfaces.append(self.text_cache['tooltip']['(Right-click to copy path)'])
				text_surfaces.append(self.text_cache['tooltip'][''])
			
				# convert '/Chip/Tower/Transistor/' to ['/Chip/', 'Tower/', 'Transistor']
				parts = self.tooltip.split('/')[1:]
				parts = [part + '/' for part in parts]
				parts[0] = '/' + parts[0]
				parts[-1] = parts[-1][:-1]
				
				for text in parts:
					if text not in self.text_cache['tooltip']:
						self.text_cache['tooltip'][text] = pygame.font.SysFont('Arial', 11).render(text, True, 'black')
					text_surfaces.append(self.text_cache['tooltip'][text])

			# normal button tool tips
			else:
				if self.tooltip not in self.text_cache['tooltip']:
					self.text_cache['tooltip'][self.tooltip] = pygame.font.SysFont('Arial', 11).render(self.tooltip, True, 'black')
				text_surfaces.append(self.text_cache['tooltip'][self.tooltip])

			self.tooltip_display_width = max([text_surface.get_size()[0] for text_surface in text_surfaces])
			self.tooltip_line_count = len(text_surfaces) 
			tooltip_rect = pygame.Rect(0, 0, self.tooltip_display_width+12, 7+13*len(text_surfaces))
			
			pygame.draw.rect(self.surfaces['tooltip'], self.colors['tooltip']['color'], tooltip_rect)
			pygame.draw.rect(self.surfaces['tooltip'], self.colors['tooltip']['outline'], tooltip_rect, 2)
			
			tooltip_top = tooltip_rect.top+3
			for text_surface in text_surfaces:		
				rect_surface = text_surface.get_rect(left=tooltip_rect.left+6, top = tooltip_top)
				self.surfaces['tooltip'].blit(text_surface, rect_surface)
				tooltip_top += 13
				
		self.last_tooltip = self.tooltip
		
	def run(self):
		"""
		Main Pygame loop to display information and poll for events
		"""		
		self.update_background()
		self.buttons_list.append(self.open_button)
		self.redraw_buttons()
				
		while 1:		
			# reset fields			
			self.mouse_pos = pygame.mouse.get_pos()
			self.tooltip = ''
			
			# button collision
			for button in self.buttons_list:
				collision = button.reference.collidepoint(self.mouse_pos)
				if collision != button.last_hover:
					button.draw(self.surfaces['buttons'], hover=collision)
					self.update_canvas = True
				if collision: self.tooltip = button.tip_text
				button.last_hover = collision

			# tree collisions
			self.tree_collision_check()
			
			# tool tips
			self.draw_tooltip()		
			if self.mouse_pos != self.last_mouse_pos and self.tooltip != '':
				self.update_canvas = True

			# event polling
			self.event_polling()
			
			# redrawing canvas
			if self.update_canvas: 
				self.redraw_canvas()
				self.update_canvas = False
				
			self.clock.tick(60) # limits FPS to 60
			self.last_mouse_pos = self.mouse_pos

# ========================================================
#    Execution
# ========================================================
if __name__ == '__main__':
	runner = KTreeViewRunner()
	runner.run()
