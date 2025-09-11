import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Alice", "Arnold", "Carol", "Peter", "Bob", "Eric"]
    phones = ["huawei p50", "iphone 13", "xiaomi mi 11", "oneplus 9", "samsung galaxy s21", "google pixel 6"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for phone_perm in itertools.permutations(phones):
            # Apply constraints
            if (name_perm[phone_perm.index("iphone 13")] == "Alice" and
                name_perm[0] == "Eric" and phone_perm[0] == "huawei p50" and
                name_perm[5] == "Arnold" and phone_perm[5] == "oneplus 9" and
                phone_perm[1] != "google pixel 6" and
                phone_perm[1] != "iphone 13" and
                abs(name_perm.index("Bob") - name_perm.index("Carol")) == 2 and
                name_perm.index("Alice") < name_perm.index("Carol") and
                name_perm[2] == "Carol" and phone_perm[2] == "xiaomi mi 11"):
                
                solution = {
                    "solution": {
                        "header": ["House", "Name", "PhoneModel"],
                        "rows": [
                            [str(house), name_perm[i], phone_perm[i]] for i, house in enumerate(houses)
                        ]
                    }
                }
                return json.dumps(solution, indent=2)

print(solve_puzzle())