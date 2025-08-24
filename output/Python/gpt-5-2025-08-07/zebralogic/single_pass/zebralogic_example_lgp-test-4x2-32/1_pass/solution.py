import itertools
import json

def solve_puzzle():
    # Define the puzzle parameters
    houses = [1, 2, 3, 4]
    names = ["Peter", "Arnold", "Eric", "Alice"]
    pets = ["bird", "fish", "dog", "cat"]

    solutions = []

    for name_perm in itertools.permutations(names):
        # Early constraints:
        # 2. Eric is not in the first house.
        # 5. Alice is not in the first house.
        if name_perm[0] in ("Eric", "Alice"):
            continue

        pos_name = {name_perm[i]: i + 1 for i in range(4)}

        for pet_perm in itertools.permutations(pets):
            pos_pet = {pet_perm[i]: i + 1 for i in range(4)}

            # 3. Eric keeps a pet bird.
            if pos_name["Eric"] != pos_pet["bird"]:
                continue

            # 6. Arnold has fish.
            if pos_name["Arnold"] != pos_pet["fish"]:
                continue

            # 4. One house between fish and Peter.
            if abs(pos_pet["fish"] - pos_name["Peter"]) != 2:
                continue

            # 1. Dog is somewhere to the right of Alice.
            if not (pos_pet["dog"] > pos_name["Alice"]):
                continue

            # All constraints satisfied; build the solution rows
            rows = []
            for h in houses:
                rows.append([str(h), name_perm[h - 1], pet_perm[h - 1]])

            solutions.append(rows)

    # Choose the first solution (should be unique)
    if not solutions:
        raise RuntimeError("No solution found for the given puzzle constraints.")

    result = {
        "solution": {
            "header": ["House", "Name", "Pet"],
            "rows": solutions[0]
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))