import z3
import json

def main():
    # Define EnumSorts
    Name, (Arnold, Eric) = z3.EnumSort('Name', ['Arnold', 'Eric'])
    Child, (Bella, Fred) = z3.EnumSort('Child', ['Bella', 'Fred'])
    Food, (GrilledCheese, Pizza) = z3.EnumSort('Food', ['grilled cheese', 'pizza'])

    # Create variables for each house
    name1 = z3.Const('name1', Name)
    child1 = z3.Const('child1', Child)
    food1 = z3.Const('food1', Food)
    name2 = z3.Const('name2', Name)
    child2 = z3.Const('child2', Child)
    food2 = z3.Const('food2', Food)

    solver = z3.Solver()

    # Add uniqueness constraints
    solver.add(name1 != name2)
    solver.add(child1 != child2)
    solver.add(food1 != food2)

    # Add clue constraints
    # Clue 1: Pizza lover is Arnold
    solver.add(z3.Implies(food1 == Pizza, name1 == Arnold))
    solver.add(z3.Implies(food2 == Pizza, name2 == Arnold))

    # Clue 2: Grilled cheese is directly left of Fred's parent
    solver.add(food1 == GrilledCheese)
    solver.add(child2 == Fred)

    # Check satisfiability
    if solver.check() == z3.sat:
        model = solver.model()
        # Extract values
        def get_str(var):
            return model.evaluate(var).decl().name()

        # House 1
        h1_name = get_str(name1)
        h1_child = get_str(child1)
        h1_food = get_str(food1)
        # House 2
        h2_name = get_str(name2)
        h2_child = get_str(child2)
        h2_food = get_str(food2)

        solution = {
            "solution": {
                "header": ["House", "Name", "Children", "Food"],
                "rows": [
                    ["1", h1_name, h1_child, h1_food],
                    ["2", h2_name, h2_child, h2_food]
                ]
            }
        }
        print(json.dumps(solution))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()