import itertools
import json

# Define the attributes available for each house.
names = ["Arnold", "Eric"]
birthdays = ["april", "sept"]
mothers = ["Aniya", "Holly"]

houses = [1, 2]

solution = None

# Generate all possible assignments for the houses.
for name_perm in itertools.permutations(names):
    for birthday_perm in itertools.permutations(birthdays):
        for mother_perm in itertools.permutations(mothers):
            # Constraint from Clue 2: The person whose birthday is in April is in the first house.
            if birthday_perm[0] != "april":
                continue

            # Constraint from Clue 1: Eric is somewhere to the left of the person whose mother's name is Holly.
            index_eric = name_perm.index("Eric")
            index_holly = mother_perm.index("Holly")
            if index_eric >= index_holly:
                continue

            # If all constraints are satisfied, record the candidate solution.
            candidate = []
            for i in range(len(houses)):
                candidate.append([str(houses[i]), name_perm[i], birthday_perm[i], mother_perm[i]])
            solution = candidate
            break
        if solution:
            break
    if solution:
        break

# Format the output according to the required JSON structure.
if solution:
    output = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother"],
            "rows": solution
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found")