from z3 import *

def solve_puzzle():
    # Define the variables
    names = ['Alice', 'Peter', 'Arnold', 'Eric']
    mothers = ['Holly', 'Kailyn', 'Janelle', 'Aniya']
    flowers = ['carnations', 'roses', 'lilies', 'daffodils']
    houses = [1, 2, 3, 4]

    # Create a solver instance
    solver = Solver()

    # Create dictionaries to map each attribute to a variable
    name_vars = {name: Int(name) for name in names}
    mother_vars = {mother: Int(mother) for mother in mothers}
    flower_vars = {flower: Int(flower) for flower in flowers}

    # Add constraints for unique assignments
    solver.add(Distinct([name_vars[name] for name in names]))
    solver.add(Distinct([mother_vars[mother] for mother in mothers]))
    solver.add(Distinct([flower_vars[flower] for flower in flowers]))

    # Add constraints for houses
    for var in list(name_vars.values()) + list(mother_vars.values()) + list(flower_vars.values()):
        solver.add(Or([var == house for house in houses]))

    # Apply the clues
    # Clue 1: Alice is The person whose mother's name is Kailyn.
    solver.add(name_vars['Alice'] == mother_vars['Kailyn'])

    # Clue 2: The person whose mother's name is Janelle is somewhere to the right of Arnold.
    solver.add(mother_vars['Janelle'] > name_vars['Arnold'])

    # Clue 3: Peter is somewhere to the right of the person who loves a carnations arrangement.
    solver.add(name_vars['Peter'] > flower_vars['carnations'])

    # Clue 4: Eric is the person who loves a bouquet of daffodils.
    solver.add(name_vars['Eric'] == flower_vars['daffodils'])

    # Clue 5: Arnold is The person whose mother's name is Holly.
    solver.add(name_vars['Arnold'] == mother_vars['Holly'])

    # Clue 6: The person who loves a carnations arrangement is somewhere to the right of The person whose mother's name is Holly.
    solver.add(flower_vars['carnations'] > mother_vars['Holly'])

    # Clue 7: The person who loves the boquet of lilies is directly left of Alice.
    solver.add(flower_vars['lilies'] == name_vars['Alice'] - 1)

    # Clue 8: Alice is in the third house.
    solver.add(name_vars['Alice'] == 3)

    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Mother", "Flower"],
                "rows": []
            }
        }

        # Create a mapping from house number to attributes
        house_to_attributes = {house: {"Name": None, "Mother": None, "Flower": None} for house in houses}

        for name, var in name_vars.items():
            house = model[var].as_long()
            house_to_attributes[house]["Name"] = name

        for mother, var in mother_vars.items():
            house = model[var].as_long()
            house_to_attributes[house]["Mother"] = mother

        for flower, var in flower_vars.items():
            house = model[var].as_long()
            house_to_attributes[house]["Flower"] = flower

        # Populate the solution rows
        for house in sorted(house_to_attributes.keys()):
            attributes = house_to_attributes[house]
            solution["solution"]["rows"].append([
                str(house),
                attributes["Name"],
                attributes["Mother"],
                attributes["Flower"]
            ])

        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

solve_puzzle()