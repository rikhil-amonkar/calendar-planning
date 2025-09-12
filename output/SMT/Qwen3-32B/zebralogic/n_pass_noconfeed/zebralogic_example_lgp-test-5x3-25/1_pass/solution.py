from z3 import *
import json

# Define EnumSorts
Names, (Arnold, Bob, Alice, Eric, Peter) = EnumSort('Names', ['Arnold', 'Bob', 'Alice', 'Eric', 'Peter'])
Heights, (very_tall, average, tall, very_short, short) = EnumSort('Heights', ['very_tall', 'average', 'tall', 'very_short', 'short'])
Foods, (stew, grilled_cheese, spaghetti, pizza, stir_fry) = EnumSort('Foods', ['stew', 'grilled_cheese', 'spaghetti', 'pizza', 'stir_fry'])

# Create variables for each house (0-based index for 5 houses)
names = [Const(f'name_{i}', Names) for i in range(5)]
heights = [Const(f'height_{i}', Heights) for i in range(5)]
foods = [Const(f'food_{i}', Foods) for i in range(5)]

solver = Solver()

# Add distinct constraints
solver.add(Distinct(names))
solver.add(Distinct(heights))
solver.add(Distinct(foods))

# Add clues
# Clue 1: Alice is short
for i in range(5):
    solver.add(Implies(names[i] == Alice, heights[i] == short))

# Clue 2: tall in house 3 (index 2)
solver.add(heights[2] == tall)

# Clue 3: average not in house 2 (index 1)
solver.add(heights[1] != average)

# Clue 4: average is left of stew
for i in range(5):
    for j in range(5):
        solver.add(Implies(And(heights[i] == average, foods[j] == stew), i < j))

# Clue 5: Arnold loves stir_fry
for i in range(5):
    solver.add(Implies(names[i] == Arnold, foods[i] == stir_fry))

# Clue 6: pizza lover is tall (house 3, index 2)
solver.add(foods[2] == pizza)

# Clue 7: Eric is in house 3 (index 2)
solver.add(names[2] == Eric)

# Clue 8: Bob is to the right of Arnold
for i in range(5):
    for j in range(5):
        solver.add(Implies(And(names[i] == Arnold, names[j] == Bob), i < j))

# Clue 9: grilled_cheese to the right of Eric (house 3, index 2)
for j in range(5):
    solver.add(Implies(foods[j] == grilled_cheese, j >= 3))  # j is index (0-4), house numbers j+1 >= 4

# Clue 10: very_short is left of Arnold
for i in range(5):
    for j in range(5):
        solver.add(Implies(And(heights[i] == very_short, names[j] == Arnold), i < j))

# Check solution
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Height", "Food"],
            "rows": []
        }
    }
    for i in range(5):
        house_num = i + 1
        name_val = model.eval(names[i]).as_string()
        height_val = model.eval(heights[i]).as_string()
        food_val = model.eval(foods[i]).as_string()
        solution["solution"]["rows"].append([str(house_num), name_val, height_val, food_val])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")