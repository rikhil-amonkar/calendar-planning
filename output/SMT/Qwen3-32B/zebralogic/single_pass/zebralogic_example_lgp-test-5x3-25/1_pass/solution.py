from z3 import *
import json

# Initialize Z3 solver
solver = Solver()

# Define variables for each house (0-based index for 5 houses)
names = [Int('names_%d' % i) for i in range(5)]
heights = [Int('heights_%d' % i) for i in range(5)]
foods = [Int('foods_%d' % i) for i in range(5)]

# Add constraints for distinct and valid range
for var_list in [names, heights, foods]:
    solver.add(Distinct(var_list))
    for i in range(5):
        solver.add(And(0 <= var_list[i], var_list[i] < 5))

# Clue 1: Alice is short (name=2, height=4)
for i in range(5):
    solver.add(Implies(names[i] == 2, heights[i] == 4))

# Clue 2: Third house is tall (index 2, height=2)
solver.add(heights[2] == 2)

# Clue 3: Average height (1) not in second house (index 1)
solver.add(heights[1] != 1)

# Clue 4: Average height is left of stew (0)
avg_index = Int('avg_index')
stew_index = Int('stew_index')
solver.add(Or([And(heights[i] == 1, avg_index == i) for i in range(5)]))
solver.add(Or([And(foods[i] == 0, stew_index == i) for i in range(5)]))
solver.add(avg_index < stew_index)

# Clue 5: Stir fry (4) is Arnold (0)
for i in range(5):
    solver.add(Implies(foods[i] == 4, names[i] == 0))

# Clue 6: Pizza (3) is tall (2)
for i in range(5):
    solver.add(Implies(foods[i] == 3, heights[i] == 2))

# Clue 7: Eric is in house 3 (index 2)
solver.add(names[2] == 3)

# Clue 8: Bob is to the right of Arnold
arnold_index = Int('arnold_index')
bob_index = Int('bob_index')
solver.add(Or([And(names[i] == 0, arnold_index == i) for i in range(5)]))
solver.add(Or([And(names[i] == 1, bob_index == i) for i in range(5)]))
solver.add(arnold_index < bob_index)

# Clue 9: Grilled cheese (1) is to the right of Eric (index 2)
grilled_cheese_index = Int('grilled_cheese_index')
solver.add(Or([And(foods[i] == 1, grilled_cheese_index == i) for i in range(5)]))
solver.add(grilled_cheese_index > 2)

# Clue 10: Very short (3) is to the left of Arnold
very_short_index = Int('very_short_index')
solver.add(Or([And(heights[i] == 3, very_short_index == i) for i in range(5)]))
solver.add(very_short_index < arnold_index)

# Check solution and build JSON
if solver.check() == sat:
    model = solver.model()
    rows = []
    for i in range(5):
        house_num = i + 1
        name_val = model.eval(names[i]).as_long()
        height_val = model.eval(heights[i]).as_long()
        food_val = model.eval(foods[i]).as_long()
        name_str = ["Arnold", "Bob", "Alice", "Eric", "Peter"][name_val]
        height_str = ["very tall", "average", "tall", "very short", "short"][height_val]
        food_str = ["stew", "grilled cheese", "spaghetti", "pizza", "stir fry"][food_val]
        rows.append([str(house_num), name_str, height_str, food_str])
    solution = {
        "solution": {
            "header": ["House", "Name", "Height", "Food"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")