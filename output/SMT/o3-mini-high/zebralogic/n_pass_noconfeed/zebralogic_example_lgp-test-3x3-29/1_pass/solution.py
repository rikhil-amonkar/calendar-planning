from z3 import *
import json

def main():
    # There are 3 houses (we use indices 0, 1, 2 corresponding to house 1,2,3)
    num_houses = 3

    # Mapping definitions:
    # Names: 0: Eric, 1: Peter, 2: Arnold
    # Mothers: 0: Holly, 1: Aniya, 2: Janelle
    # Foods: 0: grilled cheese, 1: pizza, 2: spaghetti

    # Create Z3 integer variables for each house, one per attribute.
    names = [Int(f"name_{i}") for i in range(num_houses)]
    mothers = [Int(f"mother_{i}") for i in range(num_houses)]
    foods = [Int(f"food_{i}") for i in range(num_houses)]

    solver = Solver()

    # Add domain constraints for each house: values are 0, 1, or 2.
    for i in range(num_houses):
        solver.add(And(names[i] >= 0, names[i] <= 2))
        solver.add(And(mothers[i] >= 0, mothers[i] <= 2))
        solver.add(And(foods[i] >= 0, foods[i] <= 2))

    # All houses have unique attributes.
    solver.add(Distinct(names))
    solver.add(Distinct(mothers))
    solver.add(Distinct(foods))

    # Clue 3: "The person who loves eating grilled cheese is Eric."
    # This means: if a house's food is grilled cheese (0) then that house's name is Eric (0),
    # and vice versa.
    for i in range(num_houses):
        solver.add(Implies(names[i] == 0, foods[i] == 0))
        solver.add(Implies(foods[i] == 0, names[i] == 0))

    # Clue 4: "Peter is The person whose mother's name is Holly."
    # This means: if a house's name is Peter (1) then its mother is Holly (0).
    for i in range(num_houses):
        solver.add(Implies(names[i] == 1, mothers[i] == 0))

    # Clue 2: "The person who loves eating grilled cheese is directly left of The person whose mother's name is Aniya."
    # Since houses are left-to-right (indexes 0,1,2), if a house has grilled cheese, then the very next house (i+1) must have mother Aniya (1).
    # Also, grilled cheese cannot be in the rightmost house.
    solver.add(foods[2] != 0)  # Rightmost house can't have grilled cheese.
    for i in range(num_houses - 1):
        solver.add(Implies(foods[i] == 0, mothers[i+1] == 1))

    # Clue 1: "The person who loves the spaghetti eater and Peter are next to each other."
    # Interpreting this as: "The person whose food is spaghetti is next to Peter."
    # For any house with spaghetti (2), one of its neighbors must be Peter (1).
    # For house 0, neighbor is house 1; for house 1, neighbors are houses 0 and 2; for house 2, neighbor is house 1.
    solver.add(Implies(foods[0] == 2, names[1] == 1))
    solver.add(Implies(foods[1] == 2, Or(names[0] == 1, names[2] == 1)))
    solver.add(Implies(foods[2] == 2, names[1] == 1))

    # Solve the puzzle.
    if solver.check() == sat:
        model = solver.model()
        # Define mappings from integer values to actual names.
        name_map = {0: "Eric", 1: "Peter", 2: "Arnold"}
        mother_map = {0: "Holly", 1: "Aniya", 2: "Janelle"}
        food_map = {0: "grilled cheese", 1: "pizza", 2: "spaghetti"}

        rows = []
        # Houses are in fixed order: 0 -> House "1", 1 -> House "2", 2 -> House "3"
        for i in range(num_houses):
            house_number = str(i + 1)
            name_val = model.evaluate(names[i]).as_long()
            mother_val = model.evaluate(mothers[i]).as_long()
            food_val = model.evaluate(foods[i]).as_long()
            row = [
                house_number,
                name_map[name_val],
                mother_map[mother_val],
                food_map[food_val]
            ]
            rows.append(row)

        solution = {
            "solution": {
                "header": ["House", "Name", "Mother", "Food"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()