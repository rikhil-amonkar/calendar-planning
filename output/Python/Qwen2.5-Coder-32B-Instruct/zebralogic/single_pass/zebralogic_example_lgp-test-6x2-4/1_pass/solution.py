import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Alice", "Arnold", "Carol", "Peter", "Bob", "Eric"]
    phones = ["huawei p50", "iphone 13", "xiaomi mi 11", "oneplus 9", "samsung galaxy s21", "google pixel 6"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for phone_perm in itertools.permutations(phones):
            # Create a dictionary to map house number to attributes
            house_map = {house: {"Name": name, "PhoneModel": phone} for house, name, phone in zip(houses, name_perm, phone_perm)}

            # Check all constraints
            if (house_map[1]["PhoneModel"] == "huawei p50" and
                house_map[6]["PhoneModel"] == "oneplus 9" and
                house_map[name_perm.index("Alice")]["PhoneModel"] == "iphone 13" and
                house_map[name_perm.index("Eric")]["PhoneModel"] == "huawei p50" and
                house_map[3]["PhoneModel"] == "xiaomi mi 11" and
                house_map[name_perm.index("Alice")]["House"] < house_map[name_perm.index("Carol")]["House"] and
                abs(house_map[name_perm.index("Bob")]["House"] - house_map[name_perm.index("Carol")]["House"]) == 2 and
                house_map[name_perm.index("Arnold")]["PhoneModel"] == "oneplus 9" and
                house_map[name_perm.index("Google Pixel 6")]["House"] != 2 and
                house_map[name_perm.index("iPhone 13")]["House"] != 2):

                # Prepare the solution in the required format
                solution = {
                    "solution": {
                        "header": ["House", "Name", "PhoneModel"],
                        "rows": [[str(house), house_map[house]["Name"], house_map[house]["PhoneModel"]] for house in houses]
                    }
                }

                # Output the solution as JSON
                print(json.dumps(solution, indent=2))
                return

# Run the solver
solve_puzzle()