import z3
import json

solver = z3.Solver()

# Define variables for names
eric = z3.Int('eric')
arnold = z3.Int('arnold')
peter = z3.Int('peter')
alice = 2  # Alice is in house 2 (clue 1)

# Constraints for names
solver.add(eric >= 1, eric <= 4)
solver.add(arnold >= 1, arnold <= 4)
solver.add(peter >= 1, peter <= 4)
solver.add(eric != 2, arnold != 2, peter != 2)
solver.add(z3.Distinct(eric, arnold, peter, 2))  # Alice is in house 2
solver.add(arnold > 2)  # Arnold is to the right of Craftsman (clue 4)

# Define variables for house styles
colonial = z3.Int('colonial')
ranch = z3.Int('ranch')
victorian = z3.Int('victorian')

# Constraints for house styles
solver.add(colonial >= 1, colonial <= 4)
solver.add(ranch >= 1, ranch <= 4)
solver.add(victorian >= 1, victorian <= 4)
solver.add(colonial != 2, ranch != 2, victorian != 2)  # Craftsman is in house 2
solver.add(z3.Distinct(colonial, ranch, victorian))

# Clue 2: Victorian house is directly left of Peter
solver.add(victorian + 1 == peter)

# Clue 3: Peter is to the right of the ranch-style home
solver.add(ranch < peter)

if solver.check() == z3.sat:
    model = solver.model()
    # Extract values from the model
    eric_val = model.eval(eric).as_long()
    arnold_val = model.eval(arnold).as_long()
    peter_val = model.eval(peter).as_long()
    colonial_val = model.eval(colonial).as_long()
    ranch_val = model.eval(ranch).as_long()
    victorian_val = model.eval(victorian).as_long()

    rows = []
    for house_num in range(1, 5):
        # Determine name
        if house_num == 2:
            name = 'Alice'
        else:
            if eric_val == house_num:
                name = 'Eric'
            elif arnold_val == house_num:
                name = 'Arnold'
            elif peter_val == house_num:
                name = 'Peter'
            else:
                name = 'Unknown'
        # Determine house style
        if house_num == 2:
            style = 'craftsman'
        elif colonial_val == house_num:
            style = 'colonial'
        elif ranch_val == house_num:
            style = 'ranch'
        elif victorian_val == house_num:
            style = 'victorian'
        else:
            style = 'Unknown'
        rows.append([str(house_num), name, style])

    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": rows
        }
    }

    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")