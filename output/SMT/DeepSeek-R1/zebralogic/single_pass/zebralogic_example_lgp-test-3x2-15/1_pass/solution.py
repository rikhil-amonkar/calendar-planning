from z3 import *
import json

def main():
    # Define enums for names and heights
    Name = Datatype('Name')
    Name.declare('Arnold')
    Name.declare('Peter')
    Name.declare('Eric')
    Name = Name.create()
    
    Height = Datatype('Height')
    Height.declare('short')
    Height.declare('average')
    Height.declare('very_short')
    Height = Height.create()
    
    # Create variables for each house: names[0] for house1, names[1] for house2, names[2] for house3
    names = [Const('name_%d' % i, Name) for i in range(3)]
    heights = [Const('height_%d' % i, Height) for i in range(3)]
    
    s = Solver()
    
    # All names and heights are distinct
    s.add(Distinct(names))
    s.add(Distinct(heights))
    
    # Clue 1: Peter is to the right of Eric
    s.add(Or(
        And(names[0] == Name.Eric, Or(names[1] == Name.Peter, names[2] == Name.Peter)),
        And(names[1] == Name.Eric, names[2] == Name.Peter)
    ))
    
    # Clue 2: The person who is short is in the first house
    s.add(heights[0] == Height.short)
    
    # Clue 3: One house between short and very short -> very short must be in house3 (index2)
    s.add(heights[2] == Height.very_short)
    
    # Clue 4: Arnold and the very short person are next to each other -> Arnold must be in house2 (index1)
    s.add(names[1] == Name.Arnold)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(3):
            n_val = m[names[i]]
            h_val = m[heights[i]]
            # Convert name to string
            if n_val == Name.Arnold:
                name_str = "Arnold"
            elif n_val == Name.Peter:
                name_str = "Peter"
            elif n_val == Name.Eric:
                name_str = "Eric"
            else:
                name_str = "unknown"
            # Convert height to string
            if h_val == Height.short:
                height_str = "short"
            elif h_val == Height.average:
                height_str = "average"
            elif h_val == Height.very_short:
                height_str = "very short"
            else:
                height_str = "unknown"
            rows.append([str(i+1), name_str, height_str])
        
        # Construct the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": rows
            }
        }
        # Output as JSON
        print(json.dumps(solution_dict))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()