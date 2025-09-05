from z3 import *
import json

def main():
    s = Solver()

    # Define variables for each person representing their house number (1-4)
    alice = Int('alice')
    arnold = Int('arnold')
    peter = Int('peter')
    eric = Int('eric')
    
    # Define variables for each hair color representing the house number (1-4)
    black = Int('black')
    blonde = Int('blonde')
    brown = Int('brown')
    red = Int('red')

    # Domain constraints for persons
    s.add(And(alice >= 1, alice <= 4))
    s.add(And(arnold >= 1, arnold <= 4))
    s.add(And(peter >= 1, peter <= 4))
    s.add(And(eric >= 1, eric <= 4))

    # Domain constraints for hair colors
    s.add(And(black >= 1, black <= 4))
    s.add(And(blonde >= 1, blonde <= 4))
    s.add(And(brown >= 1, brown <= 4))
    s.add(And(red >= 1, red <= 4))

    # All persons must live in different houses.
    s.add(Distinct(alice, arnold, peter, eric))
    
    # All hair colors are in different houses.
    s.add(Distinct(black, blonde, brown, red))

    # Clue 5: Alice is in the first house.
    s.add(alice == 1)

    # Clue 3: Eric is the person who has brown hair.
    s.add(eric == brown)

    # Clue 1: Eric is directly left of the person who has blonde hair.
    s.add(blonde == eric + 1)

    # Clue 2: Alice and Arnold are next to each other.
    s.add(Or(alice - arnold == 1, arnold - alice == 1))

    # Clue 4: The person who has black hair is not in the first house.
    s.add(black != 1)

    if s.check() == sat:
        m = s.model()
        # Build a mapping of house number -> attributes:
        houses = {}
        for i in range(1, 5):
            houses[i] = {"Name": None, "HairColor": None}
        
        # Map persons to their houses
        persons = [("Alice", m[alice].as_long()),
                   ("Arnold", m[arnold].as_long()),
                   ("Peter", m[peter].as_long()),
                   ("Eric", m[eric].as_long())]
        for name, house in persons:
            houses[house]["Name"] = name

        # Map hair colors to houses
        hairs = [("black", m[black].as_long()),
                 ("blonde", m[blonde].as_long()),
                 ("brown", m[brown].as_long()),
                 ("red", m[red].as_long())]
        for color, house in hairs:
            houses[house]["HairColor"] = color

        # Prepare the result in the specified JSON format.
        rows = []
        for i in range(1, 5):
            row = [str(i), houses[i]["Name"], houses[i]["HairColor"]]
            rows.append(row)

        result = {
            "solution": {
                "header": ["House", "Name", "HairColor"],
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    main()