import json
from z3 import *

# Create the Z3 solver
s = Solver()

# There are 2 houses: House 1 (left) and House 2 (right)
# We'll represent each house with two variables:
# - name: an integer that represents the person (0: Eric, 1: Arnold)
# - genre: an integer that represents the favorite book genre (0: science fiction, 1: mystery)
houses = []
for i in range(2):
    name = Int(f"name_{i+1}")
    genre = Int(f"genre_{i+1}")
    houses.append((name, genre))
    # Constraint: variables can only take the values 0 or 1.
    s.add(Or(name == 0, name == 1))
    s.add(Or(genre == 0, genre == 1))

# All houses have distinct names and distinct book genres.
s.add(Distinct(houses[0][0], houses[1][0]))
s.add(Distinct(houses[0][1], houses[1][1]))

# Clue:
# "Eric is directly left of the person who loves mystery books."
# In a row of 2 houses, the only possibility is:
# House 1 must be occupied by Eric (which is represented by 0)
# and House 2 must have mystery as the book genre (which is represented by 1).
s.add(houses[0][0] == 0)  # House 1 is Eric.
s.add(houses[1][1] == 1)  # House 2 has mystery.

# Check the solver for satisfiability and extract the model.
if s.check() == sat:
    model = s.model()

    # Mappings from integer values to the actual names and genres.
    name_map = {0: "Eric", 1: "Arnold"}
    genre_map = {0: "science fiction", 1: "mystery"}

    # Prepare the solution rows.
    result_rows = []
    for i in range(2):
        house_number = str(i+1)
        house_name = name_map[model[houses[i][0]].as_long()]
        house_genre = genre_map[model[houses[i][1]].as_long()]
        result_rows.append([house_number, house_name, house_genre])

    # Construct the final solution dictionary in the required JSON format.
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre"],
            "rows": result_rows
        }
    }

    # Output the solution as a JSON-formatted string.
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")