import json
from z3 import *

def main():
    solver = Solver()
    houses = range(1, 6)
    parent_vars = {i: Int(f"parent_{i}") for i in houses}
    child_vars = {i: Int(f"child_{i}") for i in houses}

    # Each parent's value is in the domain 0..4 and each child's value is in 0..4.
    for i in houses:
        solver.add(And(parent_vars[i] >= 0, parent_vars[i] < 5))
        solver.add(And(child_vars[i] >= 0, child_vars[i] < 5))
    
    solver.add(Distinct([parent_vars[i] for i in houses]))
    solver.add(Distinct([child_vars[i] for i in houses]))
    
    # Mappings: for parent's names: 0: Eric, 1: Alice, 2: Peter, 3: Bob, 4: Arnold
    parent_map = {
        0: "Eric",
        1: "Alice",
        2: "Peter",
        3: "Bob",
        4: "Arnold"
    }
    # Mappings: for child's names: 0: Timothy, 1: Meredith, 2: Samantha, 3: Fred, 4: Bella
    child_map = {
        0: "Timothy",
        1: "Meredith",
        2: "Samantha",
        3: "Fred",
        4: "Bella"
    }
    
    # Clue 1: Bob is somewhere to the left of the house whose child is Samantha.
    # If parent's name is Bob (3) at house i and child's name is Samantha (2) at house j, then i < j.
    for i in houses:
        for j in houses:
            solver.add(Implies(And(parent_vars[i] == 3, child_vars[j] == 2), i < j))
    
    # Clue 2: The person who is the mother of Timothy (child == 0) is somewhere to the left of the house whose child is Samantha (2).
    for i in houses:
        for j in houses:
            solver.add(Implies(And(child_vars[i] == 0, child_vars[j] == 2), i < j))
    
    # Clue 3: The house where the child is Fred (3) is the second house.
    solver.add(child_vars[2] == 3)
    
    # Clue 4: There is one house between Alice (parent == 1) and the house whose child is Samantha (2).
    for i in houses:
        for j in houses:
            solver.add(Implies(And(parent_vars[i] == 1, child_vars[j] == 2), Or(j - i == 2, i - j == 2)))
    
    # Clue 5: Eric (0) is not in the third house.
    solver.add(parent_vars[3] != 0)
    
    # Clue 6: Bob (3) is not in the third house.
    solver.add(parent_vars[3] != 3)
    
    # Clue 7: The house where the child is Fred (3) is directly left of the house whose child is Bella (4).
    for i in range(1, 5):
        solver.add(Implies(child_vars[i] == 3, child_vars[i+1] == 4))
    
    # Clue 8: The house whose child is Samantha (2) is somewhere to the left of the house with parent Peter (2).
    for i in houses:
        for j in houses:
            solver.add(Implies(And(child_vars[i] == 2, parent_vars[j] == 2), i < j))
    
    if solver.check() == sat:
        model = solver.model()
        rows = []
        for i in sorted(houses):
            parent_value = model[parent_vars[i]].as_long()
            child_value = model[child_vars[i]].as_long()
            rows.append([str(i), parent_map[parent_value], child_map[child_value]])
        output = {
            "solution": {
                "header": ["House", "Name", "Children"],
                "rows": rows
            }
        }
        print(json.dumps(output))
    else:
        print(json.dumps({"solution": {}}))

if __name__ == "__main__":
    main()