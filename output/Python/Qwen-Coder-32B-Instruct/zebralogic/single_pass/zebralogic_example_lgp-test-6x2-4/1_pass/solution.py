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
                phone_perm[0] == "huawei p50" and
                phone_perm[5] == "oneplus 9" and
                phone_perm[1] != "google pixel 6" and
                phone_perm[1] != "iphone 13" and
                abs(name_perm.index("Bob") - name_perm.index("Carol")) == 2 and
                name_perm[phone_perm.index("huawei p50")] == "Eric" and
                phone_perm[2] == "xiaomi mi 11" and
                name_perm.index("Alice") < name_perm.index("Carol") and
                name_perm[phone_perm.index("oneplus 9")] == "Arnold"):
                
                # Construct the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Phone"],
                        "rows": []
                    }
                }
                for i in range(6):
                    solution["solution"]["rows"].append([
                        str(houses[i]),
                        name_perm[i],
                        phone_perm[i]
                    ])
                return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())