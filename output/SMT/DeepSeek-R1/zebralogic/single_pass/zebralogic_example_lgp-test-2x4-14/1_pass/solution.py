from z3 import *
import json

# Initialize solver
s = Solver()

# Define variables for House 1
name1 = Int('name1')
style1 = Int('style1')
smoothie1 = Int('smoothie1')
pet1 = Int('pet1')

# Define variables for House 2
name2 = Int('name2')
style2 = Int('style2')
smoothie2 = Int('smoothie2')
pet2 = Int('pet2')

# Domain constraints and uniqueness for names
s.add(name1 >= 0, name1 <= 1)
s.add(name2 >= 0, name2 <= 1)
s.add(name1 != name2)

# Domain constraints and uniqueness for styles
s.add(style1 >= 0, style1 <= 1)
s.add(style2 >= 0, style2 <= 1)
s.add(style1 != style2)

# Domain constraints and uniqueness for smoothies
s.add(smoothie1 >= 0, smoothie1 <= 1)
s.add(smoothie2 >= 0, smoothie2 <= 1)
s.add(smoothie1 != smoothie2)

# Domain constraints and uniqueness for pets
s.add(pet1 >= 0, pet1 <= 1)
s.add(pet2 >= 0, pet2 <= 1)
s.add(pet1 != pet2)

# Clue 1: Cherry smoothie ⇔ dog owner
s.add((smoothie1 == 0) == (pet1 == 0))
s.add((smoothie2 == 0) == (pet2 == 0))

# Clue 2: Victorian house ⇔ dog owner
s.add((style1 == 0) == (pet1 == 0))
s.add((style2 == 0) == (pet2 == 0))

# Clue 3: Victorian house is left of Eric
pos_vic = If(style1 == 0, 1, 2)
pos_eric = If(name1 == 0, 1, 2)
s.add(pos_vic < pos_eric)

# Check for solution
if s.check() == sat:
    m = s.model()
    
    # Mapping functions
    def get_name(val):
        return "Eric" if val == 0 else "Arnold"
    
    def get_style(val):
        return "victorian" if val == 0 else "colonial"
    
    def get_smoothie(val):
        return "cherry" if val == 0 else "desert"
    
    def get_pet(val):
        return "dog" if val == 0 else "cat"
    
    # Extract values for House 1
    n1_val = m[name1].as_long()
    s1_val = m[style1].as_long()
    sm1_val = m[smoothie1].as_long()
    p1_val = m[pet1].as_long()
    
    # Extract values for House 2
    n2_val = m[name2].as_long()
    s2_val = m[style2].as_long()
    sm2_val = m[smoothie2].as_long()
    p2_val = m[pet2].as_long()
    
    # Create rows
    row1 = ["1", get_name(n1_val), get_style(s1_val), get_smoothie(sm1_val), get_pet(p1_val)]
    row2 = ["2", get_name(n2_val), get_style(s2_val), get_smoothie(sm2_val), get_pet(p2_val)]
    
    # Construct solution dictionary
    solution_dict = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
            "rows": [row1, row2]
        }
    }
    print(json.dumps(solution_dict))
else:
    print('{"error": "No solution found"}')