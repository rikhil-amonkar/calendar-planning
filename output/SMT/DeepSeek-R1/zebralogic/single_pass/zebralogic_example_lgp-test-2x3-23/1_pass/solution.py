from z3 import *
import json

def main():
    s = Solver()
    
    # Define the possible values
    names = ["Eric", "Arnold"]
    children = ["Bella", "Fred"]
    foods = ["grilled cheese", "pizza"]
    
    # Create string variables for house 1
    name1 = String('name1')
    child1 = String('child1')
    food1 = String('food1')
    
    # Create string variables for house 2
    name2 = String('name2')
    child2 = String('child2')
    food2 = String('food2')
    
    # Each house must have one of the names, and they must be distinct
    s.add(Or(name1 == names[0], name1 == names[1]))
    s.add(Or(name2 == names[0], name2 == names[1]))
    s.add(Distinct(name1, name2))
    
    # Each house must have one child, and they must be distinct
    s.add(Or(child1 == children[0], child1 == children[1]))
    s.add(Or(child2 == children[0], child2 == children[1]))
    s.add(Distinct(child1, child2))
    
    # Each house must have one food, and they must be distinct
    s.add(Or(food1 == foods[0], food1 == foods[1]))
    s.add(Or(food2 == foods[0], food2 == foods[1]))
    s.add(Distinct(food1, food2))
    
    # Clue 1: The person who loves pizza is Arnold.
    s.add(Implies(food1 == foods[1], name1 == names[1]))
    s.add(Implies(food2 == foods[1], name2 == names[1]))
    
    # Clue 2: The person who loves grilled cheese is directly left of the person whose child is Fred.
    # This means house 1 has grilled cheese and house 2 has child Fred.
    s.add(food1 == foods[0])
    s.add(child2 == children[1])
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Helper function to get string value from model
        def get_str_value(var):
            return m[var].as_string()
        
        # Get values for house 1
        n1 = get_str_value(name1)
        c1 = get_str_value(child1)
        f1 = get_str_value(food1)
        
        # Get values for house 2
        n2 = get_str_value(name2)
        c2 = get_str_value(child2)
        f2 = get_str_value(food2)
        
        # Construct the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Children", "Food"],
                "rows": [
                    ["1", n1, c1, f1],
                    ["2", n2, c2, f2]
                ]
            }
        }
        # Output as JSON
        print(json.dumps(solution_dict))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()