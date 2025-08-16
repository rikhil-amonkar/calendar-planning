# Solve the logic puzzle with Z3 and print the result as the required JSON
from z3 import Solver, Int, And, Or, Distinct
import json

# Domain values
names = ["Eric", "Peter", "Alice", "Arnold"]
cars = ["tesla model 3", "honda civic", "toyota camry", "ford f150"]
months = ["jan", "april", "sept", "feb"]
hobbies = ["painting", "cooking", "gardening", "photography"]

all_values = names + cars + months + hobbies

# Create Z3 Int variables for positions (1..4) for each attribute value
def var_name(v):
    return "pos_" + v.replace(" ", "_").replace("-", "_")

pos = {v: Int(var_name(v)) for v in all_values}

s = Solver()

# Domain constraints: each position in 1..4
for v in all_values:
    s.add(And(pos[v] >= 1, pos[v] <= 4))

# All-different within each category
s.add(Distinct([pos[v] for v in names]))
s.add(Distinct([pos[v] for v in cars]))
s.add(Distinct([pos[v] for v in months]))
s.add(Distinct([pos[v] for v in hobbies]))

# Clues:
# 1. The person whose birthday is in January is not in the second house.
s.add(pos["jan"] != 2)

# 2. The photography enthusiast is somewhere to the left of Eric.
s.add(pos["photography"] < pos["Eric"])

# 3. The photography enthusiast is somewhere to the left of Peter.
s.add(pos["photography"] < pos["Peter"])

# 4. The person who owns a Honda Civic is directly left of the person who owns a Tesla Model 3.
s.add(pos["honda civic"] + 1 == pos["tesla model 3"])

# 5. There is one house between the person who owns a Tesla Model 3 and the person who enjoys gardening.
s.add(Or(pos["tesla model 3"] == pos["gardening"] + 2, pos["tesla model 3"] + 2 == pos["gardening"]))

# 6. The person who owns a Tesla Model 3 is Arnold.
s.add(pos["tesla model 3"] == pos["Arnold"])

# 7. The person whose birthday is in February is the person who loves cooking.
s.add(pos["feb"] == pos["cooking"])

# 8. The person who owns a Toyota Camry is Peter.
s.add(pos["toyota camry"] == pos["Peter"])

# 9. The person whose birthday is in April is Arnold.
s.add(pos["april"] == pos["Arnold"])

# 10. Alice is the photography enthusiast.
s.add(pos["Alice"] == pos["photography"])

# 11. Peter is the person whose birthday is in January.
s.add(pos["Peter"] == pos["jan"])

# Solve
if s.check() != 1:  # 1 == sat
    raise RuntimeError("Puzzle is unsatisfiable or unknown.")

m = s.model()

# Helper to find which value is at a given house for a category
def value_at_house(values, house):
    for v in values:
        if m.evaluate(pos[v]).as_long() == house:
            return v
    return None

# Build the JSON output
solution = {
    "solution": {
        "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
        "rows": []
    }
}

for house in range(1, 5):
    row = [
        str(house),
        value_at_house(names, house),
        value_at_house(cars, house),
        value_at_house(months, house),
        value_at_house(hobbies, house),
    ]
    solution["solution"]["rows"].append(row)

print(json.dumps(solution, ensure_ascii=False))