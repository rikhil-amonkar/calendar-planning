from z3 import *

def solve_puzzle():
    solver = Solver()

    # Define variables for each house (0-based index for 4 houses)
    name = [Int(f"name_{i}") for i in range(4)]
    mother = [Int(f"mother_{i}") for i in range(4)]
    flower = [Int(f"flower_{i}") for i in range(4)]

    # Add permutation constraints
    for attr in [name, mother, flower]:
        solver.add(Distinct(attr))
        for i in range(4):
            solver.add(And(0 <= attr[i], attr[i] <= 3))

    # Known constraints
    solver.add(name[2] == 1)  # Alice in house 3 (index 2)
    solver.add(mother[2] == 1)  # Alice's mother is Kailyn
    solver.add(flower[1] == 2)  # House 2 has lilies

    # Arnold's mother is Holly
    for i in range(4):
        solver.add(Implies(name[i] == 0, mother[i] == 0))

    # Eric's favorite flower is daffodils
    for i in range(4):
        solver.add(Implies(name[i] == 3, flower[i] == 3))

    # Clue 2: Janelle's mother is to the right of Arnold
    for i in range(4):
        for j in range(4):
            solver.add(Implies(And(mother[i] == 2, name[j] == 0), i > j))

    # Clue 3: Peter is to the right of carnations lover
    for i in range(4):
        for j in range(4):
            solver.add(Implies(And(flower[i] == 0, name[j] == 2), j > i))

    # Clue 6: Carnations lover is to the right of Holly's mother (Arnold)
    for i in range(4):
        for j in range(4):
            solver.add(Implies(And(flower[i] == 0, mother[j] == 0), i > j))

    if solver.check() == sat:
        model = solver.model()
        rows = []
        for i in range(4):
            house_num = i + 1
            name_idx = model.eval(name[i]).as_long()
            mother_idx = model.eval(mother[i]).as_long()
            flower_idx = model.eval(flower[i]).as_long()
            name_str = ["Arnold", "Alice", "Peter", "Eric"][name_idx]
            mother_str = ["Holly", "Kailyn", "Janelle", "Aniya"][mother_idx]
            flower_str = ["carnations", "roses", "lilies", "daffodils"][flower_idx]
            rows.append([str(house_num), name_str, mother_str, flower_str])
        return {
            "solution": {
                "header": ["House", "Name", "Mother", "Flower"],
                "rows": rows
            }
        }
    else:
        return {"solution": {"header": [], "rows": []}}

# Example usage
solution = solve_puzzle()
import json
print(json.dumps(solution, indent=2))