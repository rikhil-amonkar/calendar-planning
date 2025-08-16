import json
from z3 import *

# Initialize the solver
s = Solver()

# Define the attributes for each house (1 and 2)
houses = [1, 2]

# Create variables for each attribute in each house
name = {house: String(f"name_{house}") for house in houses}
education = {house: String(f"education_{house}") for house in houses}
height = {house: String(f"height_{house}") for house in houses}
food = {house: String(f"food_{house}") for house in houses}
drink = {house: String(f"drink_{house}") for house in houses}

# Add constraints for uniqueness across houses for each attribute
for attr in [name, education, height, food, drink]:
    for h1 in houses:
        for h2 in houses:
            if h1 < h2:
                s.add(attr[h1] != attr[h2])

# Possible values for each attribute
names = ["Arnold", "Eric"]
educations = ["associate", "high school"]
heights = ["short", "very short"]
foods = ["grilled cheese", "pizza"]
drinks = ["tea", "water"]

# Each attribute must be one of the possible values
for house in houses:
    s.add(Or([name[house] == n for n in names]))
    s.add(Or([education[house] == e for e in educations]))
    s.add(Or([height[house] == h for h in heights]))
    s.add(Or([food[house] == f for f in foods]))
    s.add(Or([drink[house] == d for d in drinks]))

# Apply the clues
# Clue 1: The person who is very short is the person who is a pizza lover.
for house in houses:
    s.add(Implies(height[house] == "very short", food[house] == "pizza"))

# Clue 2: The person who loves eating grilled cheese is in the second house.
s.add(food[2] == "grilled cheese")

# Clue 3: The person with a high school diploma is the person who is a pizza lover.
for house in houses:
    s.add(Implies(education[house] == "high school", food[house] == "pizza"))

# Clue 4: The tea drinker is the person who loves eating grilled cheese.
for house in houses:
    s.add(Implies(food[house] == "grilled cheese", drink[house] == "tea"))

# Clue 5: Arnold is the person who is a pizza lover.
for house in houses:
    s.add(Implies(name[house] == "Arnold", food[house] == "pizza"))

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
            "rows": []
        }
    }
    for house in sorted(houses):
        row = [
            str(house),
            str(model.eval(name[house])),
            str(model.eval(education[house])),
            str(model.eval(height[house])),
            str(model.eval(food[house])),
            str(model.eval(drink[house]))
        ]
        solution["solution"]["rows"].append(row)
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")