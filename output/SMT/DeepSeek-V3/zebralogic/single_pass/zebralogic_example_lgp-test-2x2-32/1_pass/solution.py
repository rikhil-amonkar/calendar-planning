import json
from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2]

# Define the names and book genres
names = ["Eric", "Arnold"]
genres = ["science fiction", "mystery"]

# Create variables for each house's name and book genre
name_vars = {house: String(f"name_{house}") for house in houses}
genre_vars = {house: String(f"genre_{house}") for house in houses}

# Add constraints that each name and genre is unique
s.add(Distinct([name_vars[house] for house in houses]))
s.add(Distinct([genre_vars[house] for house in houses]))

# Each name and genre must be one of the allowed values
for house in houses:
    s.add(Or([name_vars[house] == name for name in names]))
    s.add(Or([genre_vars[house] == genre for genre in genres]))

# Apply the clue: Eric is directly left of the person who loves mystery books
# This means Eric is in house 1 and mystery is in house 2
s.add(name_vars[1] == "Eric")
s.add(genre_vars[2] == "mystery")

# Check if the problem is satisfiable
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre"],
            "rows": []
        }
    }
    for house in sorted(houses):
        name_val = model.eval(name_vars[house])
        genre_val = model.eval(genre_vars[house])
        solution["solution"]["rows"].append([str(house), str(name_val), str(genre_val)])
    print(json.dumps(solution, indent=2))
else:
    print(json.dumps({"error": "No solution found"}, indent=2))