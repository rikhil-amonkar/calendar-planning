import json
from z3 import *

def main():
    # Define variables for each house (0-based index)
    names = [Int(f'name_{i}') for i in range(5)]
    colors = [Int(f'color_{i}') for i in range(5)]
    phones = [Int(f'phone_{i}') for i in range(5)]
    occupations = [Int(f'occupation_{i}') for i in range(5)]

    solver = Solver()

    # Add constraints for distinct and range
    for attr in [names, colors, phones, occupations]:
        for i in range(5):
            solver.add(And(0 <= attr[i], attr[i] < 5))
        solver.add(Distinct(attr))

    # Add clues
    # Clue 2: Bob is in the second house (index 1)
    solver.add(names[1] == 0)  # Bob is 0 in names

    # Clue 3: Samsung Galaxy S21 (1) is doctor (2)
    for i in range(5):
        solver.add(Implies(phones[i] == 1, occupations[i] == 2))

    # Clue 4: Doctor (2) loves blue (0)
    for i in range(5):
        solver.add(Implies(occupations[i] == 2, colors[i] == 0))

    # Clue 5: Green (1) not in fifth house (index 4)
    for i in range(5):
        solver.add(Implies(colors[i] == 1, Not(i == 4)))

    # Clue 6: Lawyer (4) uses OnePlus 9 (2)
    for i in range(5):
        solver.add(Implies(occupations[i] == 4, phones[i] == 2))

    # Clue 7: Blue (0) directly left of red (4)
    solver.add(Or(
        And(colors[0] == 0, colors[1] == 4),
        And(colors[1] == 0, colors[2] == 4),
        And(colors[2] == 0, colors[3] == 4),
        And(colors[3] == 0, colors[4] == 4)
    ))

    # Clue 8: Lawyer (4) is to the right of Samsung Galaxy S21 (1)
    s21_idx = Int('s21_idx')
    lawyer_idx = Int('lawyer_idx')
    solver.add(Or([And(phones[i] == 1, s21_idx == i) for i in range(5)]))
    solver.add(Or([And(occupations[i] == 4, lawyer_idx == i) for i in range(5)]))
    solver.add(lawyer_idx > s21_idx)

    # Clue 1: Engineer (3) is to the right of lawyer (4)
    engineer_idx = Int('engineer_idx')
    solver.add(Or([And(occupations[i] == 3, engineer_idx == i) for i in range(5)]))
    solver.add(engineer_idx > lawyer_idx)

    # Clue 9: One house between Google Pixel 6 (4) and Huawei P50 (0)
    gp_idx = Int('gp_idx')
    hp_idx = Int('hp_idx')
    solver.add(Or([And(phones[i] == 4, gp_idx == i) for i in range(5)]))
    solver.add(Or([And(phones[i] == 0, hp_idx == i) for i in range(5)]))
    solver.add(Or(gp_idx - hp_idx == 2, hp_idx - gp_idx == 2))

    # Clue 10: Arnold (2) is engineer (3)
    for i in range(5):
        solver.add(Implies(names[i] == 2, occupations[i] == 3))

    # Clue 11: Alice (3) loves yellow (3)
    for i in range(5):
        solver.add(Implies(names[i] == 3, colors[i] == 3))

    # Clue 12: Google Pixel 6 (4) is Eric (1)
    for i in range(5):
        solver.add(Implies(phones[i] == 4, names[i] == 1))

    # Clue 13: Google Pixel 6 (4) is teacher (1)
    for i in range(5):
        solver.add(Implies(phones[i] == 4, occupations[i] == 1))

    # Clue 14: Red (4) is to the right of teacher (1)
    red_idx = Int('red_idx')
    teacher_idx = Int('teacher_idx')
    solver.add(Or([And(colors[i] == 4, red_idx == i) for i in range(5)]))
    solver.add(Or([And(occupations[i] == 1, teacher_idx == i) for i in range(5)]))
    solver.add(red_idx > teacher_idx)

    # Check solution
    if solver.check() == sat:
        model = solver.model()

        # Mapping from integer codes to strings
        name_map = {0: "Bob", 1: "Eric", 2: "Arnold", 3: "Alice", 4: "Peter"}
        color_map = {0: "blue", 1: "green", 2: "white", 3: "yellow", 4: "red"}
        phone_map = {0: "huawei p50", 1: "samsung galaxy s21", 2: "oneplus 9", 3: "iphone 13", 4: "google pixel 6"}
        occupation_map = {0: "artist", 1: "teacher", 2: "doctor", 3: "engineer", 4: "lawyer"}

        rows = []
        for i in range(5):
            house_num = i + 1
            name_val = model[names[i]].as_long()
            color_val = model[colors[i]].as_long()
            phone_val = model[phones[i]].as_long()
            occupation_val = model[occupations[i]].as_long()
            rows.append([str(house_num), name_map[name_val], color_map[color_val], phone_map[phone_val], occupation_map[occupation_val]])

        solution = {
            "solution": {
                "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
                "rows": rows
            }
        }

        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()