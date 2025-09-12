import json
from z3 import *

def main():
    # Define the names and vacations lists for mapping indices to strings
    names_list = ["Bob", "Peter", "Alice", "Eric", "Carol", "Arnold"]
    vacations_list = ["mountain", "camping", "cruise", "city", "cultural", "beach"]

    # Create Z3 variables for each house (1-6) for name and vacation
    names = [Int(f'name_{i+1}') for i in range(6)]  # names[0] is house 1
    vacations = [Int(f'vacation_{i+1}') for i in range(6)]

    s = Solver()

    # Add constraints for names and vacations to be 0-5 and distinct
    for var in names + vacations:
        s.add(And(0 <= var, var <= 5))
    s.add(Distinct(names))
    s.add(Distinct(vacations))

    # Add specific constraints based on clues
    # Clue 3: Eric is in house 2 (index 1)
    s.add(names[1] == 3)  # Eric is index 3

    # Clue 4: cultural (4) is in house 3 (index 2)
    s.add(vacations[2] == 4)

    # Clue 7: cultural is Peter (index 1) → house 3's name is Peter
    s.add(names[2] == 1)  # Peter is index 1

    # Clue 9: city (3) is in house 4 (index 3)
    s.add(vacations[3] == 3)

    # Clue 8: cruise (2) is Bob (0)
    for i in range(6):
        s.add(Implies(vacations[i] == 2, names[i] == 0))

    # Clue 6: camping (1) not in house 1 (index 0)
    s.add(vacations[0] != 1)

    # Clue 1: cultural (4) is left of beach (5) → beach is after house 3
    for i in range(6):
        s.add(Implies(vacations[i] == 5, (i + 1) > 3))

    # Clue 2: Eric (3) is to the right of Alice (2)
    eric_house = Sum([If(names[i] == 3, i + 1, 0) for i in range(6)])
    alice_house = Sum([If(names[i] == 2, i + 1, 0) for i in range(6)])
    s.add(eric_house > alice_house)

    # Clue 5: Bob (0) directly left of Arnold (5)
    clue5 = Or([And(names[i] == 0, names[i + 1] == 5) for i in range(5)])
    s.add(clue5)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        # Prepare the solution rows
        solution_rows = []
        for house_num in range(1, 7):
            # Get the index in the names and vacations lists (house_num - 1)
            name_idx = model[names[house_num - 1]].as_long()
            vacation_idx = model[vacations[house_num - 1]].as_long()
            solution_rows.append([
                str(house_num),
                names_list[name_idx],
                vacations_list[vacation_idx]
            ])

        # Construct the JSON output
        output = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": solution_rows
            }
        }

        print(json.dumps(output, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()