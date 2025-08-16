from z3 import Solver, Int, And, Distinct, sat
import json

# Create integer variables representing house positions (1 to 4) for each person.
pos_Eric = Int("pos_Eric")
pos_Arnold = Int("pos_Arnold")
pos_Alice = Int("pos_Alice")
pos_Peter = Int("pos_Peter")

# Create integer variables for each house style.
pos_craftsman = Int("pos_craftsman")
pos_colonial = Int("pos_colonial")
pos_ranch = Int("pos_ranch")
pos_victorian = Int("pos_victorian")

solver = Solver()

# All positions are in the range 1..4.
houses = [1, 2, 3, 4]
for var in [pos_Eric, pos_Arnold, pos_Alice, pos_Peter,
            pos_craftsman, pos_colonial, pos_ranch, pos_victorian]:
    solver.add(var >= 1, var <= 4)

# All people must be in different houses.
solver.add(Distinct(pos_Eric, pos_Arnold, pos_Alice, pos_Peter))

# All house styles must be assigned to different houses.
solver.add(Distinct(pos_craftsman, pos_colonial, pos_ranch, pos_victorian))

# Clue 1: Alice is in the second house.
solver.add(pos_Alice == 2)

# Clue 5: The person in a Craftsman-style house is Alice.
solver.add(pos_craftsman == pos_Alice)

# Clue 2: The person residing in a Victorian house is directly left of Peter.
solver.add(pos_victorian + 1 == pos_Peter)

# Clue 3: Peter is somewhere to the right of the person in a ranch-style home.
solver.add(pos_Peter > pos_ranch)

# Clue 4: Arnold is somewhere to the right of the person in a Craftsman-style house.
solver.add(pos_Arnold > pos_craftsman)

if solver.check() == sat:
    model = solver.model()

    # Prepare a mapping for each house
    house_assignment = {h: {"Name": None, "HouseStyle": None} for h in houses}

    # Assign names to houses.
    people = [("Eric", model[pos_Eric].as_long()),
              ("Arnold", model[pos_Arnold].as_long()),
              ("Alice", model[pos_Alice].as_long()),
              ("Peter", model[pos_Peter].as_long())]
    for name, pos in people:
        house_assignment[pos]["Name"] = name

    # Assign house styles to houses.
    styles = [("craftsman", model[pos_craftsman].as_long()),
              ("colonial", model[pos_colonial].as_long()),
              ("ranch", model[pos_ranch].as_long()),
              ("victorian", model[pos_victorian].as_long())]
    for style, pos in styles:
        house_assignment[pos]["HouseStyle"] = style

    # Build the JSON result with the required structure.
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": []
        }
    }
    for h in sorted(house_assignment.keys()):
        row = [str(h), house_assignment[h]["Name"], house_assignment[h]["HouseStyle"]]
        solution["solution"]["rows"].append(row)

    print(json.dumps(solution, indent=2))
else:
    print("No solution found")