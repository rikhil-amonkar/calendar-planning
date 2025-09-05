from z3 import *
import json

def main():
    solver = Solver()
    n = 2  # Two houses, indexed 0 and 1

    # Create Z3 integer variables for each attribute in each house.
    # For our mappings:
    # For Name: 0 => "Arnold", 1 => "Eric"
    # For Mother: 0 => "Holly", 1 => "Aniya"
    # For CarModel: 0 => "tesla model 3", 1 => "ford f150"
    # For Height: 0 => "short", 1 => "very short"
    names = [Int(f"name_{i}") for i in range(n)]
    mothers = [Int(f"mother_{i}") for i in range(n)]
    cars = [Int(f"car_{i}") for i in range(n)]
    heights = [Int(f"height_{i}") for i in range(n)]

    # Domain constraints: each variable is either 0 or 1.
    for var in names + mothers + cars + heights:
        solver.add(Or(var == 0, var == 1))

    # All houses must have distinct attributes.
    solver.add(Distinct(names[0], names[1]))
    solver.add(Distinct(mothers[0], mothers[1]))
    solver.add(Distinct(cars[0], cars[1]))
    solver.add(Distinct(heights[0], heights[1]))

    # Clue 3: The person whose mother's name is Holly is in the second house.
    # Since we mapped Holly to 0, the mother in house index 1 (House 2) must be 0.
    solver.add(mothers[1] == 0)

    # Clue 2: Arnold is the person who is short.
    # With our mapping, if a house's name is Arnold (0) then its height must be short (0).
    for i in range(n):
        solver.add(Implies(names[i] == 0, heights[i] == 0))

    # Clue 1: The person who owns a Tesla Model 3 is somewhere to the right of Arnold.
    # In a 2-house puzzle, this forces Arnold to be in the first house (index 0)
    # and the Tesla Model 3 (mapped to 0) to be in the second house (index 1).
    solver.add(names[0] == 0)
    solver.add(cars[1] == 0)

    # Solve the constraints.
    if solver.check() == sat:
        model = solver.model()
        # Define mappings from numbers to labels.
        name_map = {0: "Arnold", 1: "Eric"}
        mother_map = {0: "Holly", 1: "Aniya"}
        car_map = {0: "tesla model 3", 1: "ford f150"}
        height_map = {0: "short", 1: "very short"}

        rows = []
        # Houses are numbered from 1 to n.
        for i in range(n):
            house_number = str(i + 1)
            row = [
                house_number,
                name_map[model.evaluate(names[i]).as_long()],
                mother_map[model.evaluate(mothers[i]).as_long()],
                car_map[model.evaluate(cars[i]).as_long()],
                height_map[model.evaluate(heights[i]).as_long()]
            ]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Mother", "CarModel", "Height"],
                "rows": rows
            }
        }
        print(json.dumps(solution))
    else:
        print(json.dumps({"solution": None}))

if __name__ == '__main__':
    main()