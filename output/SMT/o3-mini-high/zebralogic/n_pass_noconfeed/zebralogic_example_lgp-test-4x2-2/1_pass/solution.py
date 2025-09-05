#!/usr/bin/env python3
import json
from z3 import *

def main():
    s = Solver()
    houses = 4

    # Create Z3 integer variables for names and house styles for each house (indexed 0 to 3 corresponding to houses 1 to 4)
    names = [Int(f"name_{i}") for i in range(houses)]
    styles = [Int(f"style_{i}") for i in range(houses)]
    
    # Domain constraints: each variable must be in the set {0, 1, 2, 3}
    for i in range(houses):
        s.add(And(names[i] >= 0, names[i] <= 3))
        s.add(And(styles[i] >= 0, styles[i] <= 3))
    
    # Uniqueness constraints: all names and all styles must be distinct.
    s.add(Distinct(names))
    s.add(Distinct(styles))
    
    # Mapping of names to integers:
    # 0: Arnold, 1: Peter, 2: Eric, 3: Alice
    #
    # Mapping of house styles to integers:
    # 0: victorian, 1: ranch, 2: colonial, 3: craftsman

    # Clue 1: Eric is the person in a Craftsman-style house.
    # For each house, if the resident is Eric (2) then the house style must be craftsman (3).
    for i in range(houses):
        s.add(Implies(names[i] == 2, styles[i] == 3))
    
    # Clue 3: Eric is in the third house.
    # House number 3 is at index 2.
    s.add(names[2] == 2)
    
    # Clue 4: Arnold is in the fourth house.
    # House number 4 is at index 3.
    s.add(names[3] == 0)
    
    # Clue 5: The person residing in a Victorian house is Alice.
    # For each house, if its style is victorian (0) then its resident must be Alice (3).
    for i in range(houses):
        s.add(Implies(styles[i] == 0, names[i] == 3))
    
    # Clue 2: The person in a ranch-style home is directly left of the person residing in a Victorian house.
    # For houses 1 to 3 (indices 0 to 2), if a house is ranch (1) then the immediately right house must be victorian (0).
    for i in range(houses - 1):
        s.add(Implies(styles[i] == 1, styles[i+1] == 0))
    # Also, the last house cannot be ranch because it wouldn't have a right neighbor.
    s.add(styles[houses - 1] != 1)
    
    if s.check() == sat:
        m = s.model()
        name_map = {0: "Arnold", 1: "Peter", 2: "Eric", 3: "Alice"}
        style_map = {0: "victorian", 1: "ranch", 2: "colonial", 3: "craftsman"}
        
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": []
            }
        }
        
        for i in range(houses):
            house_number = str(i + 1)
            house_name = name_map[m[names[i]].as_long()]
            house_style = style_map[m[styles[i]].as_long()]
            solution["solution"]["rows"].append([house_number, house_name, house_style])
        
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    main()