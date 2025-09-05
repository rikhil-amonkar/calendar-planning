import json
from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Define variables for each house
    name1 = Int('name1')
    name2 = Int('name2')
    style1 = Int('style1')
    style2 = Int('style2')
    smoothie1 = Int('smoothie1')
    smoothie2 = Int('smoothie2')
    pet1 = Int('pet1')
    pet2 = Int('pet2')
    
    # Define domains (0 or 1)
    s.add(name1 >= 0, name1 <= 1)
    s.add(name2 >= 0, name2 <= 1)
    s.add(style1 >= 0, style1 <= 1)
    s.add(style2 >= 0, style2 <= 1)
    s.add(smoothie1 >= 0, smoothie1 <= 1)
    s.add(smoothie2 >= 0, smoothie2 <= 1)
    s.add(pet1 >= 0, pet1 <= 1)
    s.add(pet2 >= 0, pet2 <= 1)
    
    # All attributes are unique per category
    s.add(name1 != name2)
    s.add(style1 != style2)
    s.add(smoothie1 != smoothie2)
    s.add(pet1 != pet2)
    
    # Clue 1: Cherry smoothie ↔ dog owner
    s.add((smoothie1 == 0) == (pet1 == 0))
    s.add((smoothie2 == 0) == (pet2 == 0))
    
    # Clue 2: Victorian house ↔ dog owner
    s.add((style1 == 0) == (pet1 == 0))
    s.add((style2 == 0) == (pet2 == 0))
    
    # Clue 3: Victorian left of Eric
    s.add(style1 == 0)  # Victorian must be in house1
    s.add(name2 == 0)   # Eric must be in house2
    
    # Check and get solution
    if s.check() == sat:
        m = s.model()
        
        # Map integer values to strings
        name_map = {0: "Eric", 1: "Arnold"}
        style_map = {0: "victorian", 1: "colonial"}
        smoothie_map = {0: "cherry", 1: "desert"}
        pet_map = {0: "dog", 1: "cat"}
        
        # Get values for house1
        n1 = name_map[m.eval(name1).as_long()]
        st1 = style_map[m.eval(style1).as_long()]
        sm1 = smoothie_map[m.eval(smoothie1).as_long()]
        p1 = pet_map[m.eval(pet1).as_long()]
        
        # Get values for house2
        n2 = name_map[m.eval(name2).as_long()]
        st2 = style_map[m.eval(style2).as_long()]
        sm2 = smoothie_map[m.eval(smoothie2).as_long()]
        p2 = pet_map[m.eval(pet2).as_long()]
        
        # Create JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
                "rows": [
                    ["1", n1, st1, sm1, p1],
                    ["2", n2, st2, sm2, p2]
                ]
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()