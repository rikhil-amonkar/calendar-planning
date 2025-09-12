from z3 import *
import json

# Initialize solver
solver = Solver()

# Define variables for each person's house
E = Int('E')  # Eric's house
A = Int('A')  # Arnold's house
P = Int('P')  # Peter's house

# Define variables for each height's house
vs = Int('vs')  # very short
s = Int('s')    # short
a = Int('a')    # average

# Constraints for people's houses
solver.add(And(1 <= E, E <= 3))
solver.add(And(1 <= A, A <= 3))
solver.add(And(1 <= P, P <= 3))
solver.add(Distinct(E, A, P))
solver.add(E != 1)  # Clue 1: Eric is not in the first house
solver.add(A != 1)  # Clue 4: Arnold is not in the first house

# Constraints for heights
solver.add(And(1 <= vs, vs <= 3))
solver.add(And(1 <= s, s <= 3))
solver.add(And(1 <= a, a <= 3))
solver.add(Distinct(vs, s, a))
solver.add(vs < s)  # Clue 2: very short is left of short
solver.add(E == vs)  # Clue 3: Eric is very short

# Check for solution
if solver.check() == sat:
    model = solver.model()
    
    # Extract values from model
    e_val = model[E].as_long()
    a_val = model[A].as_long()
    p_val = model[P].as_long()
    vs_val = model[vs].as_long()
    s_val = model[s].as_long()
    a_h_val = model[a].as_long()
    
    # Build solution rows
    rows = []
    for house_num in [1, 2, 3]:
        # Determine name
        if e_val == house_num:
            name = "Eric"
        elif a_val == house_num:
            name = "Arnold"
        else:
            name = "Peter"
            
        # Determine height
        if vs_val == house_num:
            height = "very short"
        elif s_val == house_num:
            height = "short"
        else:
            height = "average"
            
        rows.append([str(house_num), name, height])
    
    # Format as required JSON
    solution = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": rows
        }
    }
    
    print(json.dumps(solution, indent=2))
else:
    print(json.dumps({"error": "No solution found"}))