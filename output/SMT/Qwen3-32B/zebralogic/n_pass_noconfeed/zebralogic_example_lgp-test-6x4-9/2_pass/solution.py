from z3 import *

def solve_puzzle():
    solver = Solver()

    # Define variables for each house (0-based index for 6 houses)
    names = [Int(f"name_{i}") for i in range(6)]
    phone_models = [Int(f"phone_{i}") for i in range(6)]
    nationalities = [Int(f"nation_{i}") for i in range(6)]
    colors = [Int(f"color_{i}") for i in range(6)]

    # Add constraints for distinctness and domain
    for attr in [names, phone_models, nationalities, colors]:
        solver.add(Distinct(attr))
        for var in attr:
            solver.add(And(0 <= var, var <= 5))

    # Clue 1: Carol is not in the third house (index 2)
    solver.add(names[2] != 0)

    # Clue 2: One house between Dane and British
    for i in range(6):
        for j in range(6):
            solver.add(Implies(And(nationalities[i] == 3, nationalities[j] == 5), Abs(i - j) == 2))

    # Clue 3: Carol's favorite color is green
    for i in range(6):
        solver.add(Implies(names[i] == 0, colors[i] == 3))

    # Clue 4: Arnold is directly left of Alice
    solver.add(Or([And(names[i] == 3, names[i+1] == 2) for i in range(5)]))

    # Clue 5: Alice is German
    for i in range(6):
        solver.add(Implies(names[i] == 2, nationalities[i] == 4))

    # Clue 6: OnePlus 9 user loves purple
    for i in range(6):
        solver.add(Implies(phone_models[i] == 4, colors[i] == 5))

    # Clue 7: Huawei P50 not in third house
    solver.add(phone_models[2] != 3)

    # Clue 8: Samsung Galaxy S21 is in fifth house (index 4)
    solver.add(phone_models[4] == 0)

    # Clue 9: White is to the right of red
    for i in range(6):
        for j in range(6):
            solver.add(Implies(And(colors[i] == 1, colors[j] == 4), j > i))

    # Clue 10: Samsung Galaxy S21 is Bob
    solver.add(names[4] == 1)

    # Clue 11: Dane loves yellow
    for i in range(6):
        solver.add(Implies(nationalities[i] == 3, colors[i] == 2))

    # Clue 12: Samsung is left of Peter
    solver.add(Or([And(phone_models[i] == 0, names[j] == 5, j > i) for i in range(6) for j in range(6)]))

    # Clue 13: Peter loves blue
    for i in range(6):
        solver.add(Implies(names[i] == 5, colors[i] == 0))

    # Clue 14: Peter is British
    for i in range(6):
        solver.add(Implies(names[i] == 5, nationalities[i] == 5))

    # Clue 15: Samsung directly left of iPhone 13
    solver.add(Or([And(phone_models[i] == 0, phone_models[i+1] == 2) for i in range(5)]))

    # Clue 16: Norwegian loves purple
    for i in range(6):
        solver.add(Implies(nationalities[i] == 2, colors[i] == 5))

    # Clue 17: Xiaomi Mi 11 is Chinese
    for i in range(6):
        solver.add(Implies(phone_models[i] == 5, nationalities[i] == 1))

    if solver.check() == sat:
        model = solver.model()
        # Define lists for mapping indices to values
        names_list = ["Carol", "Bob", "Alice", "Arnold", "Eric", "Peter"]
        phone_list = ["samsung galaxy s21", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9", "xiaomi mi 11"]
        nation_list = ["swede", "chinese", "norwegian", "dane", "german", "brit"]
        color_list = ["blue", "red", "yellow", "green", "white", "purple"]

        rows = []
        for i in range(6):
            house_num = i + 1
            name_idx = model[names[i]].as_long()
            phone_idx = model[phone_models[i]].as_long()
            nation_idx = model[nationalities[i]].as_long()
            color_idx = model[colors[i]].as_long()
            rows.append([
                str(house_num),
                names_list[name_idx],
                phone_list[phone_idx],
                nation_list[nation_idx],
                color_list[color_idx]
            ])

        solution = {
            "solution": {
                "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
                "rows": rows
            }
        }
        import json
        return json.dumps(solution, indent=2)
    else:
        return "No solution found."

if __name__ == "__main__":
    print(solve_puzzle())