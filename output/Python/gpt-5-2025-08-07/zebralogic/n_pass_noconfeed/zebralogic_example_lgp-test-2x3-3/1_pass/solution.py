import itertools
import json

def solve_puzzle():
    # Houses numbered left to right
    houses = [1, 2]
    house_indices = {h: i for i, h in enumerate(houses)}

    # Attributes
    Names = ["Arnold", "Eric"]
    Foods = ["grilled cheese", "pizza"]
    Mothers = ["Holly", "Aniya"]

    solution = None

    # Iterate over all permutations ensuring uniqueness within each category
    for name_perm in itertools.permutations(Names):
        # Clue 2: Arnold is not in the second house.
        if name_perm[house_indices[2]] == "Arnold":
            continue

        for food_perm in itertools.permutations(Foods):
            # Clue 1: grilled cheese is directly left of pizza
            if food_perm.index("grilled cheese") + 1 != food_perm.index("pizza"):
                continue

            for mother_perm in itertools.permutations(Mothers):
                # Clue 3: Arnold is the person whose mother's name is Holly
                if name_perm.index("Arnold") != mother_perm.index("Holly"):
                    continue

                # If all constraints satisfied, record solution
                rows = []
                for h in houses:
                    i = house_indices[h]
                    rows.append([str(h), name_perm[i], food_perm[i], mother_perm[i]])
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Food", "Mother"],
                        "rows": rows
                    }
                }
                return solution  # Unique solution expected; return first found

    # If no solution found (shouldn't happen with valid puzzle), return empty structure
    return {
        "solution": {
            "header": ["House", "Name", "Food", "Mother"],
            "rows": []
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))