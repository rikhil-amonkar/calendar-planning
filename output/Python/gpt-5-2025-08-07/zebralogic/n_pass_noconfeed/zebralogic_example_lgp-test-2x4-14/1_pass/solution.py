import itertools
import json

def solve_puzzle():
    # Input variables
    houses = [1, 2]  # left to right
    names = ["Eric", "Arnold"]
    house_styles = ["victorian", "colonial"]
    smoothies = ["cherry", "desert"]
    pets = ["dog", "cat"]

    # Solve using brute-force with constraints checking
    for perm_names in itertools.permutations(names):
        for perm_styles in itertools.permutations(house_styles):
            for perm_smoothies in itertools.permutations(smoothies):
                for perm_pets in itertools.permutations(pets):
                    # Helper to find the index (house position) of a given value in a permutation
                    idx = lambda arr, val: arr.index(val)

                    # Clue 1: The Cherry smoothie person is the Dog owner.
                    if idx(perm_smoothies, "cherry") != idx(perm_pets, "dog"):
                        continue

                    # Clue 2: The Victorian house resident is the Dog owner.
                    if idx(perm_styles, "victorian") != idx(perm_pets, "dog"):
                        continue

                    # Clue 3: The Victorian house is somewhere to the left of Eric.
                    if idx(perm_styles, "victorian") >= idx(perm_names, "Eric"):
                        continue

                    # All constraints satisfied; build solution rows
                    rows = []
                    for i, h in enumerate(houses):
                        rows.append([
                            str(h),
                            perm_names[i],
                            perm_styles[i],
                            perm_smoothies[i],
                            perm_pets[i],
                        ])

                    result = {
                        "solution": {
                            "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
                            "rows": rows
                        }
                    }
                    return result

    # If no solution found (should not happen for a valid puzzle)
    return {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
            "rows": []
        }
    }

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))