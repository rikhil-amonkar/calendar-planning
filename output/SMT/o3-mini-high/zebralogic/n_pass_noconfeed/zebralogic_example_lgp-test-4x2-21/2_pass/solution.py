#!/usr/bin/env python3
from z3 import Int, Solver, Distinct, sat  # Added 'sat'
import json

def main():
    s = Solver()

    # Define house variables for each person (house numbers 1..4)
    Eric = Int('Eric')
    Arnold = Int('Arnold')
    Alice = Int('Alice')
    Peter = Int('Peter')
    persons = [Eric, Arnold, Alice, Peter]

    # Define house variables for each house style (house numbers 1..4)
    Craftsman = Int('Craftsman')
    Colonial = Int('Colonial')
    Ranch = Int('Ranch')
    Victorian = Int('Victorian')
    styles = [Craftsman, Colonial, Ranch, Victorian]

    # All variables must be in the range 1 to 4 (houses numbered 1 to 4)
    for p in persons:
        s.add(p >= 1, p <= 4)
    for st in styles:
        s.add(st >= 1, st <= 4)

    # Each person occupies a unique house.
    s.add(Distinct(Eric, Arnold, Alice, Peter))
    # Each style is assigned to a unique house.
    s.add(Distinct(Craftsman, Colonial, Ranch, Victorian))

    # Clue 1: Alice is in the second house.
    s.add(Alice == 2)

    # Clue 5: The person in a Craftsman-style house is Alice.
    # => The Craftsman house is the same as Alice's house.
    s.add(Craftsman == Alice)

    # Clue 4: Arnold is somewhere to the right of the person in a Craftsman-style house.
    s.add(Arnold > Craftsman)

    # Clue 2: The person residing in a Victorian house is directly left of Peter.
    # => Victorian house and Peter's house are consecutive: Victorian + 1 == Peter.
    s.add(Victorian + 1 == Peter)
    # The Victorian house cannot be the last house.
    s.add(Victorian < 4)

    # Clue 3: Peter is somewhere to the right of the person in a ranch-style home.
    s.add(Peter > Ranch)

    # Solve the constraints.
    if s.check() == sat:
        m = s.model()
        # Build a mapping from house number to person's name.
        house_to_name = {}
        for name, var in [('Eric', Eric), ('Arnold', Arnold), ('Alice', Alice), ('Peter', Peter)]:
            house_to_name[m.evaluate(var).as_long()] = name

        # Build a mapping from house number to house style.
        house_to_style = {}
        for style_name, var in [('craftsman', Craftsman), ('colonial', Colonial), ('ranch', Ranch), ('victorian', Victorian)]:
            house_to_style[m.evaluate(var).as_long()] = style_name

        # Construct rows sorted by house number (1 to 4).
        rows = []
        for i in range(1, 5):
            rows.append([str(i), house_to_name[i], house_to_style[i]])

        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        # In case no solution is found.
        print(json.dumps({"solution": "No solution found"}))

if __name__ == '__main__':
    main()