import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Alice", "Eric", "Bob", "Peter", "Arnold", "Carol"]
    heights = ["very tall", "tall", "super tall", "average", "very short", "short"]
    phone_models = ["oneplus 9", "google pixel 6", "samsung galaxy s21", "iphone 13", "huawei p50", "xiaomi mi 11"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for height_perm in itertools.permutations(heights):
            for phone_perm in itertools.permutations(phone_models):
                # Create a list of dictionaries for each house
                houses_info = [{"House": h, "Name": n, "Height": ht, "PhoneModel": pm}
                               for h, n, ht, pm in zip(houses, name_perm, height_perm, phone_perm)]

                # Check all constraints
                if (houses_info[names.index("Bob")]["House"] + 1 == houses_info[heights.index("tall")]["House"] and
                    houses_info[names.index("Peter")]["House"] < houses_info[phone_models.index("iphone 13")]["House"] and
                    houses_info[heights.index("very short")]["House"] > houses_info[phone_models.index("google pixel 6")]["House"] and
                    houses_info[names.index("Carol")]["Height"] == "very tall" and
                    abs(houses_info[phone_models.index("google pixel 6")]["House"] - houses_info[heights.index("short")]["House"]) == 1 and
                    houses_info[phone_models.index("samsung galaxy s21")]["House"] != 1 and
                    houses_info[phone_models.index("oneplus 9")]["House"] + 1 == houses_info[heights.index("short")]["House"] and
                    houses_info[names.index("Arnold")]["Height"] == "tall" and
                    houses_info[heights.index("super tall")]["House"] == 1 and
                    houses_info[names.index("Carol")]["PhoneModel"] == "xiaomi mi 11" and
                    houses_info[names.index("Eric")]["House"] < houses_info[phone_models.index("google pixel 6")]["House"] and
                    houses_info[heights.index("short")]["House"] == 6):
                    # If all constraints are satisfied, return the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Height", "PhoneModel"],
                            "rows": [[str(info["House"]), info["Name"], info["Height"], info["PhoneModel"]] for info in houses_info]
                        }
                    }
                    return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())