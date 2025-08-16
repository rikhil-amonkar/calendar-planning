from z3 import *
import json

def main():
    # Create string variables for each attribute of the two houses
    h1_name = String('h1_name')
    h1_style = String('h1_style')
    h1_height = String('h1_height')
    h1_edu = String('h1_edu')
    
    h2_name = String('h2_name')
    h2_style = String('h2_style')
    h2_height = String('h2_height')
    h2_edu = String('h2_edu')
    
    s = Solver()
    
    # Define the allowed values for each attribute
    names = ["Eric", "Arnold"]
    styles = ["victorian", "colonial"]
    heights = ["very short", "short"]
    edus = ["associate", "high school"]
    
    # Add constraints for house 1 attributes
    s.add(Or([h1_name == n for n in names]))
    s.add(Or([h1_style == st for st in styles]))
    s.add(Or([h1_height == h for h in heights]))
    s.add(Or([h1_edu == e for e in edus]))
    
    # Add constraints for house 2 attributes
    s.add(Or([h2_name == n for n in names]))
    s.add(Or([h2_style == st for st in styles]))
    s.add(Or([h2_height == h for h in heights]))
    s.add(Or([h2_edu == e for e in edus]))
    
    # Distinctness constraints
    s.add(h1_name != h2_name)
    s.add(h1_style != h2_style)
    s.add(h1_height != h2_height)
    s.add(h1_edu != h2_edu)
    
    # Clue 1: The short person is directly left of Eric
    s.add(h1_height == "short")
    s.add(h2_name == "Eric")
    
    # Clue 2: The Victorian house is the first house
    s.add(h1_style == "victorian")
    
    # Clue 3: The short person has an associate's degree
    s.add(Implies(h1_height == "short", h1_edu == "associate"))
    s.add(Implies(h2_height == "short", h2_edu == "associate"))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Extract values for house 1
        h1_name_val = str(m.eval(h1_name))
        h1_style_val = str(m.eval(h1_style))
        h1_height_val = str(m.eval(h1_height))
        h1_edu_val = str(m.eval(h1_edu))
        
        # Extract values for house 2
        h2_name_val = str(m.eval(h2_name))
        h2_style_val = str(m.eval(h2_style))
        h2_height_val = str(m.eval(h2_height))
        h2_edu_val = str(m.eval(h2_edu))
        
        # Prepare the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Height", "Education"],
                "rows": [
                    ["1", h1_name_val, h1_style_val, h1_height_val, h1_edu_val],
                    ["2", h2_name_val, h2_style_val, h2_height_val, h2_edu_val]
                ]
            }
        }
        # Output the solution as JSON
        print(json.dumps(solution_dict))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()