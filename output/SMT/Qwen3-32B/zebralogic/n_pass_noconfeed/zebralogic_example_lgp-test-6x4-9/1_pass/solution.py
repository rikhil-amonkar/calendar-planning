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

    # Add all the puzzle constraints
    # Clue 1: Carol is not in the third house (index 2)
    solver.add(names[2] != 0)

    # Clue 2: One house between Dane and British
    i_dane = Int('i_dane')
    i_brit = Int('i_brit')
    solver.add(And(0 <= i_dane, i_dane <= 5))
    solver.add(And(0 <= i_brit, i_brit <= 5))
    solver.add(nationalities[i_dane] == 3)
    solver.add(nationalities[i_brit] == 5)
    solver.add(Abs(i_dane - i_brit) == 2)

    # Clue 3: Carol's favorite color is green
    i_carol = Int('i_carol')
    solver.add(And(0 <= i_carol, i_carol <= 5))
    solver.add(names[i_carol] == 0)
    solver.add(colors[i_carol] == 3)

    # Clue 4: Arnold is directly left of Alice
    i_arnold = Int('i_arnold')
    i_alice = Int('i_alice')
    solver.add(And(0 <= i_arnold, i_arnold <= 5))
    solver.add(And(0 <= i_alice, i_alice <= 5))
    solver.add(names[i_arnold] == 3)
    solver.add(names[i_alice] == 2)
    solver.add(i_alice == i_arnold + 1)

    # Clue 5: Alice is German
    solver.add(nationalities[i_alice] == 4)

    # Clue 6: OnePlus 9 user loves purple
    i_oneplus = Int('i_oneplus')
    solver.add(And(0 <= i_oneplus, i_oneplus <= 5))
    solver.add(phone_models[i_oneplus] == 4)
    solver.add(colors[i_oneplus] == 5)

    # Clue 7: Huawei P50 not in third house
    solver.add(phone_models[2] != 3)

    # Clue 8: Samsung Galaxy S21 is in fifth house (index 4)
    solver.add(phone_models[4] == 0)

    # Clue 9: White is to the right of red
    i_red = Int('i_red')
    i_white = Int('i_white')
    solver.add(And(0 <= i_red, i_red <= 5))
    solver.add(And(0 <= i_white, i_white <= 5))
    solver.add(colors[i_red] == 1)
    solver.add(colors[i_white] == 4)
    solver.add(i_white > i_red)

    # Clue 10: Samsung Galaxy S21 is Bob
    solver.add(names[4] == 1)

    # Clue 11: Dane loves yellow
    solver.add(colors[i_dane] == 2)

    # Clue 12: Samsung is left of Peter
    i_peter = Int('i_peter')
    solver.add(And(0 <= i_peter, i_peter <= 5))
    solver.add(names[i_peter] == 5)
    solver.add(i_peter > 4)

    # Clue 13: Peter loves blue
    solver.add(colors[i_peter] == 0)

    # Clue 14: Peter is British
    solver.add(nationalities[i_peter] == 5)

    # Clue 15: Samsung directly left of iPhone 13
    solver.add(phone_models[5] == 2)

    # Clue 16: Norwegian loves purple
    i_norwegian = Int('i_norwegian')
    solver.add(And(0 <= i_norwegian, i_norwegian <= 5))
    solver.add(nationalities[i_norwegian] == 2)
    solver.add(colors[i_norwegian] == 5)

    # Clue 17: Xiaomi Mi 11 is Chinese
    i_xiaomi = Int('i_xiaomi')
    solver.add(And(0 <= i_xiaomi, i_xiaomi <= 5))
    solver.add(phone_models[i_xiaomi] == 5)
    solver.add(nationalities[i_xiaomi] == 1)

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