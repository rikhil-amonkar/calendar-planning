from z3 import *
import json

def main():
    solver = Solver()
    houses = 5
    
    # Create an integer variable for each attribute in each house.
    names   = [Int(f"name_{i}") for i in range(houses)]
    mothers = [Int(f"mother_{i}") for i in range(houses)]
    heights = [Int(f"height_{i}") for i in range(houses)]
    
    # Domain: Each attribute can be 0..4 representing a unique value.
    # We'll use the following mappings:
    #
    # Names:   0: "Eric",    1: "Peter",   2: "Arnold",  3: "Alice",  4: "Bob"
    # Mothers: 0: "Kailyn",  1: "Janelle", 2: "Aniya",   3: "Penny",  4: "Holly"
    # Heights: 0: "average", 1: "very short", 2: "short", 3: "very tall", 4: "tall"
    for i in range(houses):
        solver.add(And(names[i] >= 0, names[i] < 5))
        solver.add(And(mothers[i] >= 0, mothers[i] < 5))
        solver.add(And(heights[i] >= 0, heights[i] < 5))
    
    # All attributes must be unique across houses.
    solver.add(Distinct(names))
    solver.add(Distinct(mothers))
    solver.add(Distinct(heights))
    
    # Clue 1: "Alice is the person whose mother's name is Aniya."
    # Mapping: Alice = 3 and Aniya = 2.
    for i in range(houses):
        solver.add(Implies(names[i] == 3, mothers[i] == 2))
        solver.add(Implies(mothers[i] == 2, names[i] == 3))
    
    # Clue 2: "The person who has an average height is somewhere to the left of 
    # the person whose mother's name is Penny."
    # Average = 0 and Penny = 3.
    for i in range(houses):
        for j in range(houses):
            solver.add(Implies(And(heights[i] == 0, mothers[j] == 3), i < j))
    
    # Clue 3: "The person whose mother's name is Janelle is Bob."
    # Janelle = 1 and Bob = 4.
    for i in range(houses):
        solver.add(Implies(names[i] == 4, mothers[i] == 1))
        solver.add(Implies(mothers[i] == 1, names[i] == 4))
    
    # Clue 4: "Peter is not in the second house." (House indices: 0 is first, so index 1 is second)
    # Peter = 1.
    solver.add(names[1] != 1)
    
    # Clue 5: "The person who is short is directly left of Arnold."
    # Short = 2, Arnold = 2.
    # For any house j > 0, if house j is Arnold then house j-1 must be short.
    for j in range(1, houses):
        solver.add(Implies(names[j] == 2, heights[j-1] == 2))
    
    # Clue 6: "The person who is very tall is Arnold."
    # Very tall = 3.
    for i in range(houses):
        solver.add(Implies(names[i] == 2, heights[i] == 3))
        solver.add(Implies(heights[i] == 3, names[i] == 2))
    
    # Clue 7: "Bob is directly left of the person who has an average height."
    # Bob = 4 and average = 0.
    # For any house j > 0, if house j has average height then house j-1 must be Bob.
    for j in range(1, houses):
        solver.add(Implies(heights[j] == 0, names[j-1] == 4))
    # Also, if any house i (except the rightmost) is Bob then his right neighbor must have average height.
    for i in range(houses - 1):
        solver.add(Implies(names[i] == 4, heights[i+1] == 0))
    
    # Clue 8: "Eric is not in the fifth house." 
    # Eric = 0; fifth house has index 4.
    solver.add(names[4] != 0)
    
    # Clue 9: "The person who is very tall is somewhere to the right of the person whose mother's name is Holly."
    # Holly = 4.
    for i in range(houses):
        for j in range(houses):
            solver.add(Implies(And(mothers[i] == 4, heights[j] == 3), i < j))
    
    # Clue 10: "Eric is the person whose mother's name is Kailyn."
    # Eric = 0 and Kailyn = 0.
    for i in range(houses):
        solver.add(Implies(names[i] == 0, mothers[i] == 0))
        solver.add(Implies(mothers[i] == 0, names[i] == 0))
    
    # Clue 11: "The person who is very short is in the fifth house."
    # Very short = 1; fifth house index = 4.
    solver.add(heights[4] == 1)
    
    if solver.check() == sat:
        model = solver.model()
        # Define mapping dictionaries.
        names_map = {0: "Eric", 1: "Peter", 2: "Arnold", 3: "Alice", 4: "Bob"}
        mothers_map = {0: "Kailyn", 1: "Janelle", 2: "Aniya", 3: "Penny", 4: "Holly"}
        heights_map = {0: "average", 1: "very short", 2: "short", 3: "very tall", 4: "tall"}
        
        rows = []
        # Houses are numbered 1 to 5.
        for i in range(houses):
            house_number = str(i+1)
            name_val   = model[names[i]].as_long()
            mother_val = model[mothers[i]].as_long()
            height_val = model[heights[i]].as_long()
            rows.append([house_number, names_map[name_val], mothers_map[mother_val], heights_map[height_val]])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Mother", "Height"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()