import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Alice", "Eric", "Bob", "Peter", "Arnold", "Carol"]
    heights = ["very tall", "tall", "super tall", "average", "very short", "short"]
    phone_models = ["oneplus 9", "google pixel 6", "samsung galaxy s21", "iphone 13", "huawei p50", "xiaomi mi 11"]

    for name_perm in itertools.permutations(names):
        for height_perm in itertools.permutations(heights):
            for phone_perm in itertools.permutations(phone_models):
                if (name_perm.index("Bob") + 1 == name_perm.index(next(name for name, height in zip(name_perm, height_perm) if height == "tall"))) and \
                   (name_perm.index("Peter") < name_perm.index(next(name for name, phone in zip(name_perm, phone_perm) if phone == "iphone 13"))) and \
                   (name_perm.index(next(name for name, height in zip(name_perm, height_perm) if height == "very short")) > name_perm.index(next(name for name, phone in zip(name_perm, phone_perm) if phone == "google pixel 6"))) and \
                   (height_perm[name_perm.index("Carol")] == "very tall") and \
                   (abs(name_perm.index(next(name for name, phone in zip(name_perm, phone_perm) if phone == "google pixel 6")) - name_perm.index(next(name for name, height in zip(name_perm, height_perm) if height == "short"))) == 1) and \
                   (phone_perm[0] != "samsung galaxy s21") and \
                   (phone_perm.index("oneplus 9") + 1 == name_perm.index(next(name for name, height in zip(name_perm, height_perm) if height == "short"))) and \
                   (height_perm[name_perm.index("Arnold")] == "tall") and \
                   (height_perm[0] == "super tall") and \
                   (phone_perm[name_perm.index("Carol")] == "xiaomi mi 11") and \
                   (name_perm.index("Eric") < name_perm.index(next(name for name, phone in zip(name_perm, phone_perm) if phone == "google pixel 6"))) and \
                   (height_perm[5] == "short"):
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Height", "PhoneModel"],
                            "rows": [
                                [str(house), name_perm[house-1], height_perm[house-1], phone_perm[house-1]]
                                for house in houses
                            ]
                        }
                    }
                    return json.dumps(solution, indent=2)

print(solve_puzzle())