import json
import itertools

def solve_puzzle():
    # Input variables
    houses = [1, 2, 3, 4]
    names = ["Alice", "Arnold", "Peter", "Eric"]
    hair_colors = ["black", "blonde", "brown", "red"]

    # Helper
    def are_adjacent(h1, h2):
        return abs(h1 - h2) == 1

    solution = None

    for name_perm in itertools.permutations(names):
        # Map houses to names
        name_at_house = {house: name_perm[house - 1] for house in houses}
        house_of = {name_at_house[h]: h for h in houses}

        # Clue 5: Alice is in the first house.
        if house_of["Alice"] != 1:
            continue

        # Clue 2: Alice and Arnold are next to each other.
        if not are_adjacent(house_of["Alice"], house_of["Arnold"]):
            continue

        # Clue 1 requires Eric to be directly left of someone -> can't be in the last house.
        if house_of["Eric"] == 4:
            continue

        for hair_perm in itertools.permutations(hair_colors):
            hair_at_house = {house: hair_perm[house - 1] for house in houses}

            # Clue 4: The person who has black hair is not in the first house.
            if hair_at_house[1] == "black":
                continue

            # Clue 3: Eric is the person who has brown hair.
            if hair_at_house[house_of["Eric"]] != "brown":
                continue

            # Clue 1: Eric is directly left of the person who has blonde hair.
            if house_of["Eric"] + 1 > 4:
                continue
            if hair_at_house[house_of["Eric"] + 1] != "blonde":
                continue

            # If all constraints satisfied, we have a solution
            solution = {
                "name_at_house": name_at_house,
                "hair_at_house": hair_at_house
            }
            break  # Assuming unique solution

        if solution:
            break

    # Prepare JSON output
    header = ["House", "Name", "HairColor"]
    rows = []
    for h in houses:
        rows.append([str(h), solution["name_at_house"][h], solution["hair_at_house"][h]])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))