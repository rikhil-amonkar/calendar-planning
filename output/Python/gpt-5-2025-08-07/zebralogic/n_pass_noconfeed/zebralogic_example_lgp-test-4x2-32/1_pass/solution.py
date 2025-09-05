import json
from itertools import permutations

def solve_puzzle():
    # Houses numbered from left (1) to right (4)
    houses = [1, 2, 3, 4]

    # Attributes
    names = ["Peter", "Arnold", "Eric", "Alice"]
    pets = ["bird", "fish", "dog", "cat"]

    solutions = []

    # Iterate over all possible assignments of names to houses
    for name_perm in permutations(names):
        # Clue 2: Eric is not in the first house.
        if name_perm[0] == "Eric":
            continue
        # Clue 5: Alice is not in the first house.
        if name_perm[0] == "Alice":
            continue

        # Create helper mappings
        house_of_name = {name_perm[i]: i + 1 for i in range(4)}

        # Iterate over all possible assignments of pets to houses
        for pet_perm in permutations(pets):
            house_of_pet = {pet_perm[i]: i + 1 for i in range(4)}

            # Clue 3: Eric is the person who keeps a pet bird.
            if house_of_pet["bird"] != house_of_name["Eric"]:
                continue

            # Clue 6: Arnold is the person with an aquarium of fish.
            if house_of_pet["fish"] != house_of_name["Arnold"]:
                continue

            # Clue 4: There is one house between the person with fish and Peter.
            if abs(house_of_pet["fish"] - house_of_name["Peter"]) != 2:
                continue

            # Clue 1: The person who owns a dog is somewhere to the right of Alice.
            if house_of_pet["dog"] <= house_of_name["Alice"]:
                continue

            # If all constraints satisfied, record solution rows by house order
            rows = []
            for h in houses:
                rows.append([str(h), name_perm[h - 1], pet_perm[h - 1]])
            solutions.append(rows)

    # Ensure a unique solution
    if len(solutions) != 1:
        raise ValueError(f"Expected a unique solution, found {len(solutions)}")

    result = {
        "solution": {
            "header": ["House", "Name", "Pet"],
            "rows": solutions[0]
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False, indent=2))