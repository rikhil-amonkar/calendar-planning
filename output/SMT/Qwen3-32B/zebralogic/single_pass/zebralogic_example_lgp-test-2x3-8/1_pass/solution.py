import z3
import json

# Define EnumSorts
Name, (Arnold, Eric) = z3.EnumSort('Name', ['Arnold', 'Eric'])
Mother, (Aniya, Holly) = z3.EnumSort('Mother', ['Aniya', 'Holly'])
Birthday, (april, sept) = z3.EnumSort('Birthday', ['april', 'sept'])

# Create variables for each house
# House 1
name_1 = z3.Const('name_1', Name)
mother_1 = z3.Const('mother_1', Mother)
birthday_1 = z3.Const('birthday_1', Birthday)

# House 2
name_2 = z3.Const('name_2', Name)
mother_2 = z3.Const('mother_2', Mother)
birthday_2 = z3.Const('birthday_2', Birthday)

solver = z3.Solver()

# Add constraints

# Clue 2: birthday_1 is april
solver.add(birthday_1 == april)
# birthday_2 must be sept
solver.add(birthday_2 == sept)

# Names are distinct
solver.add(name_1 != name_2)

# Mothers are distinct
solver.add(mother_1 != mother_2)

# Clue 1: Eric is left of mother Holly. So name_1 is Eric and mother_2 is Holly
solver.add(name_1 == Eric)
solver.add(mother_2 == Holly)

# Check if satisfiable
if solver.check() == z3.sat:
    model = solver.model()
    # Now extract values for each house
    # House 1:
    n1 = model[name_1].name()
    m1 = model[mother_1].name()
    b1 = model[birthday_1].name()
    # House 2:
    n2 = model[name_2].name()
    m2 = model[mother_2].name()
    b2 = model[birthday_2].name()
    # Now build the JSON structure
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother"],
            "rows": [
                ["1", n1, b1, m1],
                ["2", n2, b2, m2]
            ]
        }
    }
    print(json.dumps(solution))
else:
    print("No solution")