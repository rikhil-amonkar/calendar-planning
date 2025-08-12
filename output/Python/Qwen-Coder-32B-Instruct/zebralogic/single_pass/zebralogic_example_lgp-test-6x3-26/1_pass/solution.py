import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Alice", "Eric", "Bob", "Peter", "Arnold", "Carol"]
    heights = ["very tall", "tall", "super tall", "average", "very short", "short"]
    phones = ["oneplus 9", "google pixel 6", "samsung galaxy s21", "iphone 13", "huawei p50", "xiaomi mi 11"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for height_perm in itertools.permutations(heights):
            for phone_perm in itertools.permutations(phones):
                # Create a list of dictionaries for each house
                solution = [
                    {"House": str(h), "Name": n, "Height": hgt, "Phone": phn}
                    for h, n, hgt, phn in zip(houses, name_perm, height_perm, phone_perm)
                ]

                # Check constraints
                if (name_perm.index("Bob") + 1 == name_perm.index(next(n for n, h in zip(name_perm, height_perm) if h == "tall"))) and \
                   (name_perm.index("Peter") < name_perm.index(next(n for n, p in zip(name_perm, phone_perm) if p == "iphone 13"))) and \
                   (name_perm.index(next(n for n, h in zip(name_perm, height_perm) if h == "very short")) > name_perm.index(next(n for n, p in zip(name_perm, phone_perm) if p == "google pixel 6"))) and \
                   (height_perm[name_perm.index("Carol")] == "very tall") and \
                   (abs(name_perm.index(next(n for n, p in zip(name_perm, phone_perm) if p == "google pixel 6")) - name_perm.index(next(n for n, h in zip(name_perm, height_perm) if h == "short"))) == 1) and \
                   (phone_perm[0] != "samsung galaxy s21") and \
                   (name_perm.index(next(n for n, p in zip(name_perm, phone_perm) if p == "oneplus 9")) + 1 == name_perm.index(next(n for n, h in zip(name_perm, height_perm) if h == "short"))) and \
                   (height_perm[name_perm.index("Arnold")] == "tall") and \
                   (height_perm[0] == "super tall") and \
                   (phone_perm[name_perm.index("Carol")] == "xiaomi mi 11") and \
                   (name_perm.index(next(n for n, p in zip(name_perm, phone_perm) if p == "google pixel 6")) > name_perm.index("Eric")) and \
                   (height_perm[5] == "short"):
                    # If all constraints are satisfied, return the solution in JSON format
                    return json.dumps({
                        "solution": {
                            "header": ["House", "Name", "Height", "Phone"],
                            "rows": [[str(s["House"]), s["Name"], s["Height"], s["Phone"]] for s in solution]
                        }
                    })

# Solve the puzzle and print the result
print(solve_puzzle())