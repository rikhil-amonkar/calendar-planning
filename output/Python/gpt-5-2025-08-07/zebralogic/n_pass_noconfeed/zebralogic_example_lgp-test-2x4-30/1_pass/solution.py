import itertools
import json

def solve_puzzle():
    # Input variables
    houses = [1, 2]
    names = ["Arnold", "Eric"]
    hair_colors = ["black", "brown"]
    sports = ["basketball", "soccer"]
    smoothies = ["desert", "cherry"]

    solutions = []

    # Iterate over all possible assignments
    for name_assign in itertools.permutations(names):
        for hair_assign in itertools.permutations(hair_colors):
            # Clue 3: Arnold is somewhere to the left of the person who has black hair.
            if name_assign.index("Arnold") >= hair_assign.index("black"):
                continue

            for sport_assign in itertools.permutations(sports):
                # Clue 2: The person who has brown hair is the person who loves basketball.
                if hair_assign.index("brown") != sport_assign.index("basketball"):
                    continue

                for smoothie_assign in itertools.permutations(smoothies):
                    # Clue 1: The Desert smoothie lover is Arnold.
                    if smoothie_assign.index("desert") != name_assign.index("Arnold"):
                        continue

                    # If all constraints satisfied, record solution
                    solution_rows = []
                    for i, house in enumerate(houses):
                        row = [
                            str(house),
                            name_assign[i],
                            hair_assign[i],
                            sport_assign[i],
                            smoothie_assign[i],
                        ]
                        solution_rows.append(row)
                    solutions.append(solution_rows)

    # Expect a unique solution
    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")
    if len(solutions) > 1:
        # In case multiple solutions are found (shouldn't happen with given constraints),
        # pick the first to maintain valid output format.
        selected = solutions[0]
    else:
        selected = solutions[0]

    output = {
        "solution": {
            "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
            "rows": selected
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))