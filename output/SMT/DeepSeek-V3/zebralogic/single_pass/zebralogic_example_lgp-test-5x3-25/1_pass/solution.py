import json
from z3 import *

# Create the solver
s = Solver()

# Define the houses
houses = [1, 2, 3, 4, 5]

# Define the attributes
names = ["Arnold", "Bob", "Alice", "Eric", "Peter"]
heights = ["very tall", "average", "tall", "very short", "short"]
foods = ["stew", "grilled cheese", "spaghetti", "pizza", "stir fry"]

# Create variables for each attribute in each house
name_vars = {h: String(f"name_{h}") for h in houses}
height_vars = {h: String(f"height_{h}") for h in houses}
food_vars = {h: String(f"food_{h}") for h in houses}

# Each attribute must be one of the possible values
for h in houses:
    s.add(Or([name_vars[h] == name for name in names]))
    s.add(Or([height_vars[h] == height for height in heights]))
    s.add(Or([food_vars[h] == food for food in foods]))

# All names, heights, and foods must be unique
s.add(Distinct([name_vars[h] for h in houses]))
s.add(Distinct([height_vars[h] for h in houses]))
s.add(Distinct([food_vars[h] for h in houses]))

# Apply the clues
# 1. Alice is the person who is short.
for h in houses:
    s.add(Implies(name_vars[h] == "Alice", height_vars[h] == "short"))

# 2. The person who is tall is in the third house.
s.add(height_vars[3] == "tall")

# 3. The person who has an average height is not in the second house.
s.add(Not(height_vars[2] == "average"))

# 4. The person who has an average height is somewhere to the left of the person who loves the stew.
# Find house with average height and house with stew, and ensure average < stew
average_house = Int("average_house")
stew_house = Int("stew_house")
s.add(Or([And(height_vars[h] == "average", average_house == h) for h in houses]))
s.add(Or([And(food_vars[h] == "stew", stew_house == h) for h in houses]))
s.add(average_house < stew_house)

# 5. The person who loves stir fry is Arnold.
for h in houses:
    s.add(Implies(food_vars[h] == "stir fry", name_vars[h] == "Arnold"))

# 6. The person who is a pizza lover is the person who is tall.
for h in houses:
    s.add(Implies(food_vars[h] == "pizza", height_vars[h] == "tall"))

# 7. Eric is the person who is tall.
for h in houses:
    s.add(Implies(name_vars[h] == "Eric", height_vars[h] == "tall"))

# 8. Bob is somewhere to the right of Arnold.
arnold_house = Int("arnold_house")
bob_house = Int("bob_house")
s.add(Or([And(name_vars[h] == "Arnold", arnold_house == h) for h in houses]))
s.add(Or([And(name_vars[h] == "Bob", bob_house == h) for h in houses]))
s.add(arnold_house < bob_house)

# 9. The person who loves grilled cheese is somewhere to the right of Eric.
eric_house = Int("eric_house")
grilled_cheese_house = Int("grilled_cheese_house")
s.add(Or([And(name_vars[h] == "Eric", eric_house == h) for h in houses]))
s.add(Or([And(food_vars[h] == "grilled cheese", grilled_cheese_house == h) for h in houses]))
s.add(eric_house < grilled_cheese_house)

# 10. The person who is very short is somewhere to the left of Arnold.
very_short_house = Int("very_short_house")
s.add(Or([And(height_vars[h] == "very short", very_short_house == h) for h in houses]))
s.add(very_short_house < arnold_house)

# Check if the problem is satisfiable
if s.check() == sat:
    model = s.model()
    
    # Prepare the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Height", "Food"],
            "rows": []
        }
    }
    
    # Collect the results for each house
    for h in houses:
        name = model.eval(name_vars[h]).as_string()
        height = model.eval(height_vars[h]).as_string()
        food = model.eval(food_vars[h]).as_string()
        solution["solution"]["rows"].append([str(h), name, height, food])
    
    # Print the JSON solution
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")