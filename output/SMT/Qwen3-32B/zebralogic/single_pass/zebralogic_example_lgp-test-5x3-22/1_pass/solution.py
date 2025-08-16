from z3 import *
import json

def solve_puzzle():
    name_list = ['Arnold', 'Eric', 'Bob', 'Peter', 'Alice']
    smoothie_list = ['desert', 'watermelon', 'lime', 'cherry', 'dragonfruit']
    nationality_list = ['german', 'swede', 'dane', 'norwegian', 'brit']

    names = [Int(f'name_{i}') for i in range(5)]
    smoothies = [Int(f'smoothie_{i}') for i in range(5)]
    nationalities = [Int(f'nationality_{i}') for i in range(5)]

    s = Solver()

    # Add distinct constraints
    s.add(Distinct(names))
    s.add(Distinct(smoothies))
    s.add(Distinct(nationalities))

    # Add range constraints
    for i in range(5):
        s.add(And(0 <= names[i], names[i] < 5))
        s.add(And(0 <= smoothies[i], smoothies[i] < 5))
        s.add(And(0 <= nationalities[i], nationalities[i] < 5))

    # Fixed constraints
    s.add(smoothies[1] == 4)  # House 2: dragonfruit
    s.add(names[2] == 4)       # House 3: Alice
    s.add(nationalities[2] == 3)  # House 3: norwegian
    s.add(smoothies[2] == 1)   # House 3: watermelon
    s.add(nationalities[0] == 1)  # House 1: swede
    s.add(names[0] != 3)       # Peter not in first house

    # Clue 4: Dane and Brit adjacent
    for i in range(5):
        if i == 0:
            s.add(Implies(names[i] == 2, nationalities[1] == 4))
        elif i == 4:
            s.add(Implies(names[i] == 2, nationalities[3] == 4))
        else:
            s.add(Implies(names[i] == 2, Or(nationalities[i-1] == 4, nationalities[i+1] == 4)))

    # Clue 7: two houses between Dane (Bob) and Lime
    for i in range(5):
        clauses = []
        if i - 3 >= 0:
            clauses.append(smoothies[i - 3] == 2)
        if i + 3 < 5:
            clauses.append(smoothies[i + 3] == 2)
        if clauses:
            s.add(Implies(names[i] == 2, Or(clauses)))

    # Clue 5: desert not in fifth house
    s.add(smoothies[4] != 0)

    # Clue 1: Eric to the right of Dragonfruit (house 2, index 1)
    for i in range(5):
        s.add(Implies(names[i] == 1, i >= 2))

    if s.check() == sat:
        model = s.model()
        rows = []
        for i in range(5):
            house_num = i + 1
            name_idx = model[names[i]].as_long()
            name = name_list[name_idx]
            smoothie_idx = model[smoothies[i]].as_long()
            smoothie = smoothie_list[smoothie_idx]
            nat_idx = model[nationalities[i]].as_long()
            nat = nationality_list[nat_idx]
            rows.append([str(house_num), name, smoothie, nat])
        return {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Nationality"],
                "rows": rows
            }
        }
    else:
        return None  # No solution

# Generate and print the solution
solution = solve_puzzle()
print(json.dumps(solution, indent=2))