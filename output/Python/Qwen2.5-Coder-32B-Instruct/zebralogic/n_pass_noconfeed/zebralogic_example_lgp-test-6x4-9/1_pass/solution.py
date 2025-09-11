import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Carol", "Bob", "Alice", "Arnold", "Eric", "Peter"]
    phone_models = ["samsung galaxy s21", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9", "xiaomi mi 11"]
    nationalities = ["swede", "chinese", "norwegian", "dane", "german", "brit"]
    colors = ["blue", "red", "yellow", "green", "white", "purple"]

    for name_perm in itertools.permutations(names):
        for phone_model_perm in itertools.permutations(phone_models):
            for nationality_perm in itertools.permutations(nationalities):
                for color_perm in itertools.permutations(colors):
                    # Assign permutations to houses
                    house_info = list(zip(houses, name_perm, phone_model_perm, nationality_perm, color_perm))

                    # Check all constraints
                    if (house_info[2][1] != "Carol" and
                        abs(house_info.index((next(h for h in house_info if h[3] == "dane"))) -
                            house_info.index((next(h for h in house_info if h[3] == "brit")))) == 2 and
                        house_info[house_info.index((next(h for h in house_info if h[1] == "Carol")))][4] == "green" and
                        house_info.index((next(h for h in house_info if h[1] == "Arnold"))) + 1 ==
                        house_info.index((next(h for h in house_info if h[1] == "Alice"))) and
                        house_info[house_info.index((next(h for h in house_info if h[1] == "Alice")))][3] == "german" and
                        house_info[house_info.index((next(h for h in house_info if h[2] == "oneplus 9")))][4] == "purple" and
                        house_info[2][2] != "huawei p50" and
                        house_info[4][2] == "samsung galaxy s21" and
                        house_info.index((next(h for h in house_info if h[4] == "white"))) >
                        house_info.index((next(h for h in house_info if h[4] == "red"))) and
                        house_info[house_info.index((next(h for h in house_info if h[2] == "samsung galaxy s21")))][1] == "Bob" and
                        house_info[house_info.index((next(h for h in house_info if h[3] == "dane")))][4] == "yellow" and
                        house_info.index((next(h for h in house_info if h[2] == "samsung galaxy s21"))) <
                        house_info.index((next(h for h in house_info if h[1] == "Peter"))) and
                        house_info[house_info.index((next(h for h in house_info if h[1] == "Peter")))][4] == "blue" and
                        house_info[house_info.index((next(h for h in house_info if h[1] == "Peter")))][3] == "brit" and
                        house_info.index((next(h for h in house_info if h[2] == "samsung galaxy s21"))) + 1 ==
                        house_info.index((next(h for h in house_info if h[2] == "iphone 13"))) and
                        house_info[house_info.index((next(h for h in house_info if h[4] == "purple")))][3] == "norwegian" and
                        house_info[house_info.index((next(h for h in house_info if h[3] == "chinese")))][2] == "xiaomi mi 11"):
                        
                        # If all constraints are satisfied, format the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
                                "rows": [[str(h), n, pm, nat, col] for h, n, pm, nat, col in house_info]
                            }
                        }
                        return json.dumps(solution, indent=2)

# Run the solver and print the solution
print(solve_puzzle())