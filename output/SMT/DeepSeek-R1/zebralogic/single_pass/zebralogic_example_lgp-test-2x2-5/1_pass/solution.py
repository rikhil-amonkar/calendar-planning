from z3 import *
import json

def main():
    # Define the enums for Name and HouseStyle
    Name, (Eric, Arnold) = EnumSort('Name', ['Eric', 'Arnold'])
    Style, (victorian, colonial) = EnumSort('Style', ['victorian', 'colonial'])
    
    # Create variables for the two houses
    name1 = Const('name1', Name)
    name2 = Const('name2', Name)
    style1 = Const('style1', Style)
    style2 = Const('style2', Style)
    
    s = Solver()
    
    # All names and styles must be unique
    s.add(Distinct(name1, name2))
    s.add(Distinct(style1, style2))
    
    # Clue 1: Victorian is left of colonial -> house1 is victorian, house2 is colonial
    s.add(style1 == victorian)
    s.add(style2 == colonial)
    
    # Clue 2: Eric is in the first house
    s.add(name1 == Eric)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Mapping from Z3 constants to strings
        name_map = {Eric: "Eric", Arnold: "Arnold"}
        style_map = {victorian: "victorian", colonial: "colonial"}
        
        # Extract values for house 1
        name_val1 = m[name1]
        style_val1 = m[style1]
        row1 = ["1", name_map[name_val1], style_map[style_val1]]
        
        # Extract values for house 2
        name_val2 = m[name2]
        style_val2 = m[style2]
        row2 = ["2", name_map[name_val2], style_map[style_val2]]
        
        # Construct the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": [row1, row2]
            }
        }
        print(json.dumps(solution_dict))
    else:
        # Print an error if no solution is found
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()