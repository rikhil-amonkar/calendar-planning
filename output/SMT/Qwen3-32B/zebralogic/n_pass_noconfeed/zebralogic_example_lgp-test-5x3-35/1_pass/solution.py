import z3
import json

# Initialize Z3 solver
s = z3.Solver()

# Create variables for each house (0-based index)
names = [z3.Int(f'name_{i}') for i in range(5)]
mothers = [z3.Int(f'mother_{i}') for i in range(5)]
heights = [z3.Int(f'height_{i}') for i in range(5)]

# Add constraints for uniqueness and valid ranges
for var_list in [names, mothers, heights]:
    s.add(z3.Distinct(var_list))
    for v in var_list:
        s.add(z3.And(0 <= v, v < 5))

# Add constraints based on the clues
# Clue 1: Alice is the person whose mother is Aniya (mother=2)
for i in range(5):
    s.add(z3.Implies(mothers[i] == 2, names[i] == 3))

# Clue 2: Average height (0) is left of Penny's mother (3)
clue2 = z3.Or([z3.And(heights[i] == 0, mothers[j] == 3, i < j) 
               for i in range(5) for j in range(5) if i < j])
s.add(clue2)

# Clue 3: Janelle's mother (1) is Bob (4)
for i in range(5):
    s.add(z3.Implies(mothers[i] == 1, names[i] == 4))

# Clue 4: Peter (1) is not in the second house (index 1)
s.add(names[1] != 1)

# Clue 5: Short (2) is directly left of Arnold (2)
clue5 = z3.Or([z3.And(heights[i] == 2, names[i+1] == 2) for i in range(4)])
s.add(clue5)

# Clue 6: Arnold (2) is very tall (3)
for i in range(5):
    s.add(z3.Implies(names[i] == 2, heights[i] == 3))

# Clue 7: Bob (4) is directly left of average height (0)
clue7 = z3.Or([z3.And(names[i] == 4, heights[i+1] == 0) for i in range(4)])
s.add(clue7)

# Clue 8: Eric (0) is not in the fifth house (index 4)
s.add(names[4] != 0)

# Clue 9: Very tall (3) is right of Holly's mother (4)
clue9 = z3.Or([z3.And(mothers[j] == 4, heights[i] == 3, i > j) 
               for i in range(5) for j in range(5)])
s.add(clue9)

# Clue 10: Eric (0) has mother Kailyn (0)
for i in range(5):
    s.add(z3.Implies(names[i] == 0, mothers[i] == 0))

# Clue 11: Very short (1) is in the fifth house (index 4)
s.add(heights[4] == 1)

# Check for solution
if s.check() == z3.sat:
    model = s.model()
    
    # Mapping integer codes to actual values
    name_map = {0: 'Eric', 1: 'Peter', 2: 'Arnold', 3: 'Alice', 4: 'Bob'}
    mother_map = {0: 'Kailyn', 1: 'Janelle', 2: 'Aniya', 3: 'Penny', 4: 'Holly'}
    height_map = {0: 'average', 1: 'very short', 2: 'short', 3: 'very tall', 4: 'tall'}
    
    # Build solution rows
    solution_rows = []
    for i in range(5):
        house_num = str(i + 1)
        name_val = name_map[model[names[i]].as_long()]
        mother_val = mother_map[model[mothers[i]].as_long()]
        height_val = height_map[model[heights[i]].as_long()]
        solution_rows.append([house_num, name_val, mother_val, height_val])
    
    # Output JSON
    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "Height"],
            "rows": solution_rows
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")