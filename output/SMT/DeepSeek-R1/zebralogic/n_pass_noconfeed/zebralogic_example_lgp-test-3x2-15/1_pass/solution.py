from z3 import *
import json

def main():
    # Initialize the solver
    s = Solver()
    
    # Houses
    houses = [1, 2, 3]
    
    # Attributes mapping
    names = {"Arnold": 0, "Peter": 1, "Eric": 2}
    heights = {"short": 0, "average": 1, "very short": 2}
    
    # Reverse mapping for output
    rev_names = {v: k for k, v in names.items()}
    rev_heights = {v: k for k, v in heights.items()}
    
    # Define variables for each house: name and height
    n1, n2, n3 = Ints('n1 n2 n3')
    h1, h2, h3 = Ints('h1 h2 h3')
    
    # All variables must be within their domain
    s.add(n1 >= 0, n1 <= 2)
    s.add(n2 >= 0, n2 <= 2)
    s.add(n3 >= 0, n3 <= 2)
    s.add(h1 >= 0, h1 <= 2)
    s.add(h2 >= 0, h2 <= 2)
    s.add(h3 >= 0, h3 <= 2)
    
    # All names and heights are distinct
    s.add(Distinct(n1, n2, n3))
    s.add(Distinct(h1, h2, h3))
    
    # Clue 1: Peter is somewhere to the right of Eric.
    # Peter=1, Eric=2. So position of Peter > position of Eric.
    s.add(Or(
        And(n1 == 2, Or(n2 == 1, n3 == 1)),  # Eric in house 1, Peter in 2 or 3
        And(n2 == 2, n3 == 1)                 # Eric in house 2, Peter in 3
    ))
    
    # Clue 2: The person who is short is in the first house.
    s.add(h1 == heights["short"])
    
    # Clue 3: One house between short and very short.
    # Since short is in house 1, very short must be in house 3.
    s.add(h3 == heights["very short"])
    
    # Clue 4: Arnold and the person who is very short are next to each other.
    # Very short is in house 3, so Arnold must be in house 2.
    s.add(n2 == names["Arnold"])
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        
        # Retrieve values for each house
        solution_rows = []
        for i, (n_var, h_var) in enumerate([(n1, h1), (n2, h2), (n3, h3)]):
            house_num = i + 1
            name_val = m.evaluate(n_var).as_long()
            height_val = m.evaluate(h_var).as_long()
            
            name_str = rev_names[name_val]
            height_str = rev_heights[height_val]
            
            solution_rows.append([str(house_num), name_str, height_str])
        
        # Format the solution as JSON
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": solution_rows
            }
        }
        
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()