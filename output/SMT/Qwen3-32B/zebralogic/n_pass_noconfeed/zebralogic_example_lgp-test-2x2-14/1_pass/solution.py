import z3
import json

def main():
    # Define Enum Sorts
    Name, (Eric, Arnold) = z3.EnumSort('Name', ['Eric', 'Arnold'])
    Food, (Pizza, GrilledCheese) = z3.EnumSort('Food', ['pizza', 'grilled_cheese'])

    # Create variables for each house's attributes
    name_h1 = z3.Const('name_h1', Name)
    food_h1 = z3.Const('food_h1', Food)
    name_h2 = z3.Const('name_h2', Name)
    food_h2 = z3.Const('food_h2', Food)

    solver = z3.Solver()

    # Add constraints for uniqueness
    solver.add(name_h1 != name_h2)
    solver.add(food_h1 != food_h2)

    # Add puzzle clues as constraints
    solver.add(food_h2 == Pizza)  # Clue 1
    solver.add(name_h1 != Arnold)  # Clue 2

    if solver.check() == z3.sat:
        model = solver.model()
        # Extract values for each house
        name_h1_val = model.evaluate(name_h1).decl().name()
        food_h1_val = model.evaluate(food_h1).decl().name()
        name_h2_val = model.evaluate(name_h2).decl().name()
        food_h2_val = model.evaluate(food_h2).decl().name()

        # Build the solution dictionary
        solution = {
            "solution": {
                "header": ["House", "Name", "Food"],
                "rows": [
                    ["1", name_h1_val, food_h1_val],
                    ["2", name_h2_val, food_h2_val]
                ]
            }
        }

        # Print as JSON
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()