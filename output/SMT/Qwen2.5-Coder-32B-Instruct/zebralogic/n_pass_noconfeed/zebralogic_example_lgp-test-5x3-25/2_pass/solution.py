from z3 import *

# Define the domains
houses = [1, 2, 3, 4, 5]
names = ["Arnold", "Bob", "Alice", "Eric", "Peter"]
heights = ["very tall", "average", "tall", "very short", "short"]
foods = ["stew", "grilled cheese", "spaghetti", "pizza", "stir fry"]

# Create the solver
solver = Solver()

# Declare variables
name_vars = {house: Int(f"name_{house}") for house in houses}
height_vars = {house: Int(f"height_{house}") for house in houses}
food_vars = {house: Int(f"food_{house}") for house in houses}

# Add domain constraints
for house in houses:
    solver.add(name_vars[house] >= 0)
    solver.add(name_vars[house] < len(names))
    solver.add(height_vars[house] >= 0)
    solver.add(height_vars[house] < len(heights))
    solver.add(food_vars[house] >= 0)
    solver.add(food_vars[house] < len(foods))

# All names, heights, and foods must be unique
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([height_vars[house] for house in houses]))
solver.add(Distinct([food_vars[house] for house in houses]))

# Clue constraints
# 1. Alice is the person who is short.
alice_idx = names.index("Alice")
short_idx = heights.index("short")
solver.add(Exists([Int('house')], And(name_vars[Int('house')] == alice_idx, height_vars[Int('house')] == short_idx)))

# 2. The person who is tall is in the third house.
tall_idx = heights.index("tall")
solver.add(height_vars[3] == tall_idx)

# 3. The person who has an average height is not in the second house.
avg_idx = heights.index("average")
solver.add(height_vars[2] != avg_idx)

# 4. The person who has an average height is somewhere to the left of the person who loves the stew.
stew_idx = foods.index("stew")
solver.add(Or(
    And(height_vars[1] == avg_idx, Or(food_vars[2] == stew_idx, food_vars[3] == stew_idx, food_vars[4] == stew_idx, food_vars[5] == stew_idx)),
    And(height_vars[2] == avg_idx, Or(food_vars[3] == stew_idx, food_vars[4] == stew_idx, food_vars[5] == stew_idx)),
    And(height_vars[3] == avg_idx, Or(food_vars[4] == stew_idx, food_vars[5] == stew_idx)),
    And(height_vars[4] == avg_idx, food_vars[5] == stew_idx)
))

# 5. The person who loves stir fry is Arnold.
arnold_idx = names.index("Arnold")
stir_fry_idx = foods.index("stir fry")
solver.add(Exists([Int('house')], And(name_vars[Int('house')] == arnold_idx, food_vars[Int('house')] == stir_fry_idx)))

# 6. The person who is a pizza lover is the person who is tall.
pizza_idx = foods.index("pizza")
solver.add(Exists([Int('house')], And(food_vars[Int('house')] == pizza_idx, height_vars[Int('house')] == tall_idx)))

# 7. Eric is the person who is tall.
eric_idx = names.index("Eric")
solver.add(Exists([Int('house')], And(name_vars[Int('house')] == eric_idx, height_vars[Int('house')] == tall_idx)))

# 8. Bob is somewhere to the right of Arnold.
bob_idx = names.index("Bob")
solver.add(Or(
    And(name_vars[1] == arnold_idx, Or(name_vars[2] == bob_idx, name_vars[3] == bob_idx, name_vars[4] == bob_idx, name_vars[5] == bob_idx)),
    And(name_vars[2] == arnold_idx, Or(name_vars[3] == bob_idx, name_vars[4] == bob_idx, name_vars[5] == bob_idx)),
    And(name_vars[3] == arnold_idx, Or(name_vars[4] == bob_idx, name_vars[5] == bob_idx)),
    And(name_vars[4] == arnold_idx, name_vars[5] == bob_idx)
))

# 9. The person who loves eating grilled cheese is somewhere to the right of Eric.
grilled_cheese_idx = foods.index("grilled cheese")
solver.add(Or(
    And(name_vars[1] == eric_idx, Or(food_vars[2] == grilled_cheese_idx, food_vars[3] == grilled_cheese_idx, food_vars[4] == grilled_cheese_idx, food_vars[5] == grilled_cheese_idx)),
    And(name_vars[2] == eric_idx, Or(food_vars[3] == grilled_cheese_idx, food_vars[4] == grilled_cheese_idx, food_vars[5] == grilled_cheese_idx)),
    And(name_vars[3] == eric_idx, Or(food_vars[4] == grilled_cheese_idx, food_vars[5] == grilled_cheese_idx)),
    And(name_vars[4] == eric_idx, food_vars[5] == grilled_cheese_idx)
))

# 10. The person who is very short is somewhere to the left of Arnold.
very_short_idx = heights.index("very short")
solver.add(Or(
    And(height_vars[1] == very_short_idx, Or(name_vars[2] == arnold_idx, name_vars[3] == arnold_idx, name_vars[4] == arnold_idx, name_vars[5] == arnold_idx)),
    And(height_vars[2] == very_short_idx, Or(name_vars[3] == arnold_idx, name_vars[4] == arnold_idx, name_vars[5] == arnold_idx)),
    And(height_vars[3] == very_short_idx, Or(name_vars[4] == arnold_idx, name_vars[5] == arnold_idx)),
    And(height_vars[4] == very_short_idx, name_vars[5] == arnold_idx)
))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Height", "Food"],
            "rows": []
        }
    }
    for house in houses:
        name = names[model.evaluate(name_vars[house]).as_long()]
        height = heights[model.evaluate(height_vars[house]).as_long()]
        food = foods[model.evaluate(food_vars[house]).as_long()]
        solution["solution"]["rows"].append([str(house), name, height, food])
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")