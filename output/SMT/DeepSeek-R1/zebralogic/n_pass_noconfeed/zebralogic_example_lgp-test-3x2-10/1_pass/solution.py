import json
from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Define enums for attributes
    Name = Datatype('Name')
    Name.declare('Eric')
    Name.declare('Arnold')
    Name.declare('Peter')
    Name = Name.create()
    
    Height = Datatype('Height')
    Height.declare('very_short')
    Height.declare('short')
    Height.declare('average')
    Height = Height.create()
    
    # Create constants for attribute values
    Eric = Name.Eric
    Arnold = Name.Arnold
    Peter = Name.Peter
    very_short = Height.very_short
    short = Height.short
    average = Height.average
    
    # Create variables for each house's attributes
    names = [Const(f'n_{i}', Name) for i in range(3)]
    heights = [Const(f'h_{i}', Height) for i in range(3)]
    
    # Add uniqueness constraints
    s.add(Distinct(names))
    s.add(Distinct(heights))
    
    # Clue 1: Eric is not in the first house
    s.add(names[0] != Eric)
    
    # Clue 2: Very short is left of short
    # Find positions of very_short and short
    very_short_pos = Int('very_short_pos')
    short_pos = Int('short_pos')
    s.add(very_short_pos >= 0, very_short_pos <= 2)
    s.add(short_pos >= 0, short_pos <= 2)
    for i in range(3):
        s.add(If(heights[i] == very_short, very_short_pos == i, True))
        s.add(If(heights[i] == short, short_pos == i, True))
    s.add(very_short_pos < short_pos)
    
    # Clue 3: Very short is Eric
    for i in range(3):
        s.add(If(heights[i] == very_short, names[i] == Eric, True))
    
    # Clue 4: Arnold is not in first house
    s.add(names[0] != Arnold)
    
    # Check solution
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(3):
            name_val = m.eval(names[i])
            height_val = m.eval(heights[i])
            
            # Convert name to string
            if name_val == Eric:
                name_str = "Eric"
            elif name_val == Arnold:
                name_str = "Arnold"
            else:
                name_str = "Peter"
            
            # Convert height to string
            if height_val == very_short:
                height_str = "very short"
            elif height_val == short:
                height_str = "short"
            else:
                height_str = "average"
            
            rows.append([str(i+1), name_str, height_str])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()