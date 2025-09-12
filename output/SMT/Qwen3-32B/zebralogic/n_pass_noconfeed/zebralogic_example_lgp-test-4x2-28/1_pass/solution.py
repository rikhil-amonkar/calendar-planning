import z3
import json

# Define the enum sorts for names and hair colors
Name, (Alice, Arnold, Peter, Eric) = z3.EnumSort('Name', ['Alice', 'Arnold', 'Peter', 'Eric'])
HairColor, (black, blonde, brown, red) = z3.EnumSort('HairColor', ['black', 'blonde', 'brown', 'red'])

# Create variables for each house's name and hair color (houses 1-4)
names_in_houses = [z3.Const(f'name_{i+1}', Name) for i in range(4)]
hairs_in_houses = [z3.Const(f'hair_{i+1}', HairColor) for i in range(4)]

solver = z3.Solver()

# All names are distinct
solver.add(z3.Distinct(names_in_houses))
# All hair colors are distinct
solver.add(z3.Distinct(hairs_in_houses))

# Clue 5: Alice is in the first house
solver.add(names_in_houses[0] == Alice)

# Clue 2: Alice and Arnold are next to each other. Since Alice is in house 1, Arnold must be in house 2
solver.add(names_in_houses[1] == Arnold)

# Clue 4: The person with black hair is not in the first house
solver.add(hairs_in_houses[0] != black)

# Clue 3: Eric has brown hair
for i in range(4):
    solver.add(z3.Implies(names_in_houses[i] == Eric, hairs_in_houses[i] == brown))

# Clue 1: Eric is directly left of the person with blonde hair
for i in range(3):  # houses 1, 2, 3 (indices 0, 1, 2)
    solver.add(z3.Implies(names_in_houses[i] == Eric, hairs_in_houses[i+1] == blonde))

if solver.check() == z3.sat:
    model = solver.model()
    # Prepare the solution data
    solution_data = {
        "solution": {
            "header": ["House", "Name", "HairColor"],
            "rows": []
        }
    }
    for i in range(4):
        house_num = i + 1
        name = str(model.eval(names_in_houses[i]))
        hair_color = str(model.eval(hairs_in_houses[i]))
        solution_data["solution"]["rows"].append([str(house_num), name, hair_color])
    # Output as JSON
    print(json.dumps(solution_data, indent=2))
else:
    print("No solution found.")