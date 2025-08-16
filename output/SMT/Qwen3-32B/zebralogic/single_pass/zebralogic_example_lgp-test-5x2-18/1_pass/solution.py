from z3 import *

def solve_puzzle():
    solver = Solver()

    # Create variables for each house (1-5)
    name = [Int(f'name_{i}') for i in range(1, 6)]  # indexes 0-4 for houses 1-5
    child = [Int(f'child_{i}') for i in range(1, 6)]

    # All names and children are unique and in 0-4
    solver.add(Distinct(name))
    solver.add(Distinct(child))
    for i in range(5):
        solver.add(And(0 <= name[i], name[i] < 5))
        solver.add(And(0 <= child[i], child[i] < 5))

    # Clue 3: child in house 2 is Fred (3)
    solver.add(child[1] == 3)  # house 2 is index 1

    # Clue 7: Fred directly left of Bella (so house 3 is Bella, index 2)
    solver.add(child[2] == 4)  # Bella is 4

    # Clue 4: One house between Alice and Samantha's house
    solver.add(Implies(child[0] == 2, name[2] == 1))  # house 1 and 3
    solver.add(Implies(child[3] == 2, name[1] == 1))  # house 4 and 2
    solver.add(Implies(child[4] == 2, name[2] == 1))  # house 5 and 3

    # Clue 1: Bob (3) is left of Samantha's house
    for i in range(5):  # i is index of Samantha's house
        for j in range(5):  # j is index of Bob's house
            solver.add(Implies(And(child[i] == 2, name[j] == 3), j < i))

    # Clue 2: Mother of Timothy (child 0) is left of Samantha's house
    for i in range(5):  # i is index of Timothy's house
        for k in range(5):  # k is index of Samantha's house
            solver.add(Implies(And(child[i] == 0, child[k] == 2), i < k))

    # Clue 8: Samantha's house (child 2) is left of Peter (name 2)
    for i in range(5):  # i is Samantha's index
        for j in range(5):  # j is Peter's index
            solver.add(Implies(And(child[i] == 2, name[j] == 2), i < j))

    # Clue 5: Eric (0) not in house 3 (index 2)
    solver.add(name[2] != 0)

    # Clue 6: Bob (3) not in house 3 (index 2)
    solver.add(name[2] != 3)

    if solver.check() == sat:
        model = solver.model()
        solution = []
        for i in range(5):
            house_num = i + 1
            n = model[name[i]].as_long()
            c = model[child[i]].as_long()
            name_str = ["Eric", "Alice", "Peter", "Bob", "Arnold"][n]
            child_str = ["Timothy", "Meredith", "Samantha", "Fred", "Bella"][c]
            solution.append([str(house_num), name_str, child_str])
        return {
            "solution": {
                "header": ["House", "Name", "Children"],
                "rows": solution
            }
        }
    else:
        return None

# Call the function and print the JSON result
result = solve_puzzle()
import json
print(json.dumps(result, indent=2))