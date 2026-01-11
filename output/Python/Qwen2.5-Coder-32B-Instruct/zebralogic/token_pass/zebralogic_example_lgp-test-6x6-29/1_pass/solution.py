import itertools
import json

# Define possible values for each attribute
names = ['Arnold', 'Carol', 'Peter', 'Eric', 'Bob', 'Alice']
house_styles = ['ranch', 'colonial', 'modern', 'craftsman', 'mediterranean', 'victorian']
foods = ['pizza', 'stew', 'spaghetti', 'grilled cheese', 'stir fry', 'soup']
vacations = ['cultural', 'cruise', 'mountain', 'camping', 'city', 'beach']
heights = ['average', 'very tall', 'very short', 'short', 'tall', 'super tall']
cigars = ['yellow monster', 'prince', 'dunhill', 'pall mall', 'blue master', 'blends']

# Function to check if the current state satisfies all constraints
def is_valid(state):
    # Unpack state
    (name_order, house_style_order, food_order, vacation_order, height_order, cigar_order) = state
    
    # Check individual house assignments
    if name_order[4] != 'Alice': return False
    if food_order[house_style_order.index('colonial')] != 'stir fry': return False
    if food_order[name_order.index('Alice')] != 'spaghetti': return False
    if food_order[name_order.index('Arnold')] != 'stew': return False
    if name_order[height_order.index('average')] not in [name_order[i] for i in [name_order.index('Peter')-1, name_order.index('Peter')+1]]: return False
    if house_style_order[2] == 'craftsman': return False
    if food_order[height_order.index('average')] != 'stir fry': return False
    if house_style_order[vacation_order.index('beach')] != 'ranch': return False
    if name_order[3] != 'Eric': return False
    if abs(house_style_order.index('colonial') - vacation_order.index('camping')) != 2: return False
    if vacation_order[cigar_order.index('yellow monster')] != 'mountain': return False
    if height_order[vacation_order.index('mountain')] != 'very tall': return False
    if abs(vacation_order.index('mountain') - cigar_order.index('dunhill')) == 1: return False
    if food_order[house_style_order.index('victorian')] != 'spaghetti': return False
    if height_order[vacation_order.index('beach')] != 'tall': return False
    if house_style_order.index('victorian') < name_order.index(height_order.index('tall')): return False
    if food_order.index('stir fry') != name_order.index('Bob') - 1: return False
    if house_style_order.index('modern') > name_order.index('Alice'): return False
    if house_style_order.index('craftsman') > height_order.index('short'): return False
    if food_order.index('stir fry') > cigar_order.index('prince'): return False
    if abs(food_order.index('grilled cheese') - height_order.index('super tall')) == 2: return False
    if cigar_order[house_style_order.index('ranch')] != 'blue master': return False
    if cigar_order.index('blue master') != cigar_order.index('blends') + 1: return False
    if food_order[vacation_order.index('cultural')] != 'pizza': return False
    if food_order.index('pizza') > vacation_order.index('cruise'): return False
    
    return True

# Generate all permutations and find the valid one
for name_order in itertools.permutations(names):
    for house_style_order in itertools.permutations(house_styles):
        for food_order in itertools.permutations(foods):
            for vacation_order in itertools.permutations(vacations):
                for height_order in itertools.permutations(heights):
                    for cigar_order in itertools.permutations(cigars):
                        state = (name_order, house_style_order, food_order, vacation_order, height_order, cigar_order)
                        if is_valid(state):
                            # Construct the solution in the required JSON format
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"],
                                    "rows": []
                                }
                            }
                            for i in range(6):
                                solution["solution"]["rows"].append([
                                    str(i+1),
                                    name_order[i],
                                    house_style_order[i],
                                    food_order[i],
                                    vacation_order[i],
                                    height_order[i],
                                    cigar_order[i]
                                ])
                            
                            print(json.dumps(solution, indent=2))
                            exit()