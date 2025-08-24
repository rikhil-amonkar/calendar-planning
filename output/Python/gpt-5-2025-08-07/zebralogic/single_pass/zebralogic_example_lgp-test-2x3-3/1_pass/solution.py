import itertools
import json

def solve_puzzle():
    # Input variables (puzzle constraints)
    houses = [1, 2]  # left to right
    names = ["Arnold", "Eric"]
    foods = ["grilled cheese", "pizza"]
    mothers = ["Holly", "Aniya"]

    solutions = []

    # Iterate over all permutations for each category
    for name_assign in itertools.permutations(names, len(houses)):
        # Clue 2: Arnold is not in the second house.
        if name_assign[1] == "Arnold":
            continue

        for food_assign in itertools.permutations(foods, len(houses)):
            # Clue 1: grilled cheese is directly left of pizza
            # For houses [1,2], this means:
            # index(grilled cheese) == index(pizza) - 1
            if food_assign.index("grilled cheese") != food_assign.index("pizza") - 1:
                continue

            for mother_assign in itertools.permutations(mothers, len(houses)):
                # Clue 3: Arnold is the person whose mother's name is Holly.
                if name_assign.index("Arnold") != mother_assign.index("Holly"):
                    continue

                # All constraints satisfied; record solution
                solution = {
                    "name": list(name_assign),
                    "food": list(food_assign),
                    "mother": list(mother_assign),
                }
                solutions.append(solution)

    # Assuming a unique solution exists; take the first valid one
    if not solutions:
        raise ValueError("No solution found with the given constraints.")
    sol = solutions[0]

    # Build output structure
    result = {
        "solution": {
            "header": ["House", "Name", "Food", "Mother"],
            "rows": [
                [str(houses[i]), sol["name"][i], sol["food"][i], sol["mother"][i]]
                for i in range(len(houses))
            ]
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))