#!/usr/bin/env python3
import json
from z3 import Solver, Int, Distinct, sat

def main():
    solver = Solver()

    # Define variables for persons (their house number)
    alice = Int('alice')
    peter = Int('peter')
    arnold = Int('arnold')
    eric = Int('eric')

    # Define variables for mothers (their house number)
    holly = Int('holly')
    kailyn = Int('kailyn')
    janelle = Int('janelle')
    aniya = Int('aniya')

    # Define variables for flowers (their house number)
    carnations = Int('carnations')
    roses = Int('roses')
    lilies = Int('lilies')
    daffodils = Int('daffodils')

    # All variables must be in the domain 1..4.
    variables = [alice, peter, arnold, eric,
                 holly, kailyn, janelle, aniya,
                 carnations, roses, lilies, daffodils]
    for var in variables:
        solver.add(var >= 1, var <= 4)

    # Ensure each category has all different house numbers
    solver.add(Distinct(alice, peter, arnold, eric))
    solver.add(Distinct(holly, kailyn, janelle, aniya))
    solver.add(Distinct(carnations, roses, lilies, daffodils))
    
    # Puzzle constraints:
    # 1. Alice is the person whose mother's name is Kailyn.
    solver.add(alice == kailyn)
    # 2. The person whose mother's name is Janelle is somewhere to the right of Arnold.
    solver.add(janelle > arnold)
    # 3. Peter is somewhere to the right of the person who loves a carnations arrangement.
    solver.add(peter > carnations)
    # 4. Eric is the person who loves a bouquet of daffodils.
    solver.add(eric == daffodils)
    # 5. Arnold is the person whose mother's name is Holly.
    solver.add(arnold == holly)
    # 6. The person who loves a carnations arrangement is somewhere to the right of the person whose mother's name is Holly.
    solver.add(carnations > holly)
    # 7. The person who loves the bouquet of lilies is directly left of Alice.
    solver.add(lilies + 1 == alice)
    # 8. Alice is in the third house.
    solver.add(alice == 3)

    if solver.check() == sat:
        model = solver.model()
        # Prepare a mapping for each house number from 1 to 4.
        houses = {i: {"Name": None, "Mother": None, "Flower": None} for i in range(1, 5)}
        
        # Map persons to their house
        persons = [
            ("Alice", model[alice].as_long()),
            ("Peter", model[peter].as_long()),
            ("Arnold", model[arnold].as_long()),
            ("Eric", model[eric].as_long())
        ]
        for name, pos in persons:
            houses[pos]["Name"] = name

        # Map mothers to their house
        mothers = [
            ("Holly", model[holly].as_long()),
            ("Kailyn", model[kailyn].as_long()),
            ("Janelle", model[janelle].as_long()),
            ("Aniya", model[aniya].as_long())
        ]
        for mother, pos in mothers:
            houses[pos]["Mother"] = mother

        # Map flowers to their house
        flowers = [
            ("carnations", model[carnations].as_long()),
            ("roses", model[roses].as_long()),
            ("lilies", model[lilies].as_long()),
            ("daffodils", model[daffodils].as_long())
        ]
        for flower, pos in flowers:
            houses[pos]["Flower"] = flower

        # Prepare the JSON output
        header = ["House", "Name", "Mother", "Flower"]
        rows = []
        for i in range(1, 5):
            row = [str(i), houses[i]["Name"], houses[i]["Mother"], houses[i]["Flower"]]
            rows.append(row)
        result = {"solution": {"header": header, "rows": rows}}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()