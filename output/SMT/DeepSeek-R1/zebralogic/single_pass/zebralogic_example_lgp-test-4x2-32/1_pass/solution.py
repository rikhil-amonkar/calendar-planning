from z3 import *
import json

def main():
    # Define variables for names and pets for 4 houses (index 0: house1, index1: house2, etc.)
    names = [Int('name_%d' % i) for i in range(4)]
    pets = [Int('pet_%d' % i) for i in range(4)]
    
    s = Solver()
    
    # Each name and pet must be between 0 and 3
    for i in range(4):
        s.add(And(names[i] >= 0, names[i] < 4))
        s.add(And(pets[i] >= 0, pets[i] < 4))
    
    # Names are all different and pets are all different
    s.add(Distinct(names))
    s.add(Distinct(pets))
    
    # Clue 2: Eric is not in the first house -> Eric (2) not at house1 (index0)
    s.add(names[0] != 2)
    
    # Clue 5: Alice is not in the first house -> Alice (3) not at house1 (index0)
    s.add(names[0] != 3)
    
    # Clue 3: Eric (2) has the bird (0)
    for i in range(4):
        s.add(If(names[i] == 2, pets[i] == 0, True))
    
    # Clue 6: Arnold (1) has the fish (1)
    for i in range(4):
        s.add(If(names[i] == 1, pets[i] == 1, True))
    
    # Clue 4: One house between fish (1) and Peter (0)
    # We use: |position_fish - position_peter| = 2
    # Represented as: (fish at i and Peter at i+2) or (fish at i and Peter at i-2) for valid i
    positions = range(4)
    or_conditions = []
    for i in positions:
        for j in positions:
            or_conditions.append(And(pets[i] == 1, names[j] == 0, Or(i == j+2, j == i+2)))
    s.add(Or(or_conditions))
    
    # Clue 1: Dog (2) is to the right of Alice (3)
    # For each house i, if Alice is at i, then dog must be at some j>i
    for i in range(4):
        # If Alice is at house i, then there must be a dog in a house j>i
        s.add(If(names[i] == 3, Or([pets[j] == 2 for j in range(i+1, 4)]), True))
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        name_vals = [m.evaluate(names[i]).as_long() for i in range(4)]
        pet_vals = [m.evaluate(pets[i]).as_long() for i in range(4)]
        
        # Mapping integers to strings
        name_map = {0: 'Peter', 1: 'Arnold', 2: 'Eric', 3: 'Alice'}
        pet_map = {0: 'bird', 1: 'fish', 2: 'dog', 3: 'cat'}
        
        # Build the rows for the solution
        rows = []
        for i in range(4):
            house_num = str(i+1)
            name_str = name_map[name_vals[i]]
            pet_str = pet_map[pet_vals[i]]
            rows.append([house_num, name_str, pet_str])
        
        # Create the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Pet"],
                "rows": rows
            }
        }
        
        # Output as JSON
        print(json.dumps(solution_dict))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()