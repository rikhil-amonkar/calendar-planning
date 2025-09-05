from z3 import *
import json

def main():
    s = Solver()
    
    # Houses are numbered 1 to 5 (we use 0-indexed for arrays: 0->House1, 1->House2, ...)
    houses = list(range(5))
    
    # Create Z3 integer variables for names and heights for each house.
    # Domains for names: 0:Peter, 1:Alice, 2:Bob, 3:Eric, 4:Arnold
    name_vars = [Int(f"name_{i}") for i in houses]
    # Domains for heights: 0:very tall, 1:average, 2:tall, 3:very short, 4:short
    height_vars = [Int(f"height_{i}") for i in houses]
    
    # Add domain constraints for names and heights.
    for nv in name_vars:
        s.add(nv >= 0, nv <= 4)
    for hv in height_vars:
        s.add(hv >= 0, hv <= 4)
    
    # All names and heights are distinct.
    s.add(Distinct(name_vars))
    s.add(Distinct(height_vars))
    
    # Define constant values for names.
    peter_val = 0
    alice_val = 1
    bob_val   = 2
    eric_val  = 3
    arnold_val= 4
    
    # Define constant values for heights.
    very_tall_val  = 0
    average_val    = 1
    tall_val       = 2
    very_short_val = 3
    short_val      = 4
    
    # Clue 1: The person who is short is in the second house.
    s.add(height_vars[1] == short_val)
    
    # Clue 7: The person who has an average height is in the fifth house.
    s.add(height_vars[4] == average_val)
    
    # Clue 2: Peter is directly left of Bob.
    # This means there exists an index i (0<=i<=3) such that house[i] is Peter and house[i+1] is Bob.
    s.add(Or([And(name_vars[i] == peter_val, name_vars[i+1] == bob_val) for i in range(4)]))
    
    # Clue 3: Eric is somewhere to the left of Peter.
    # Since each appears exactly once, we can sum the house indices (i+1) weighted by a condition.
    s.add(
        Sum([If(name_vars[i] == eric_val, i+1, 0) for i in range(5)]) <
        Sum([If(name_vars[i] == peter_val, i+1, 0) for i in range(5)])
    )
    
    # Clue 4: The person who is very tall is directly left of Peter.
    # There exists an index i (0<=i<=3) such that house[i+1] is Peter and house[i] has height "very tall".
    s.add(Or([And(name_vars[i+1] == peter_val, height_vars[i] == very_tall_val) for i in range(4)]))
    
    # Clue 5: Alice is directly left of the person who has an average height.
    # Since average height is in the fifth house, Alice must be in the fourth house.
    s.add(name_vars[3] == alice_val)
    
    # Clue 6: The person who is short and the person who is very short are next to each other.
    # The short person is in house2 (index 1), so very short must be in house1 (index 0) or house3 (index 2).
    s.add(Or(height_vars[0] == very_short_val, height_vars[2] == very_short_val))
    
    # Solve the puzzle.
    if s.check() == sat:
        m = s.model()
        # Mapping for names and heights.
        names_list = ["Peter", "Alice", "Bob", "Eric", "Arnold"]
        heights_list = ["very tall", "average", "tall", "very short", "short"]
        
        rows = []
        for i in range(5):
            house_number = str(i+1)
            name_val = m.evaluate(name_vars[i]).as_long()
            height_val = m.evaluate(height_vars[i]).as_long()
            row = [house_number, names_list[name_val], heights_list[height_val]]
            rows.append(row)
            
        solution = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": "No solution found."}))

if __name__ == "__main__":
    main()