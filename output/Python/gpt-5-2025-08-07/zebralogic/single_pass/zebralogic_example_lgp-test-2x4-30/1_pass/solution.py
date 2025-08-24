import itertools
import json

def solve_puzzle():
    # Input variables
    houses = [1, 2]  # left (1) to right (2)
    names = ["Arnold", "Eric"]
    hair_colors = ["black", "brown"]
    sports = ["basketball", "soccer"]
    smoothies = ["desert", "cherry"]

    solutions_rows = []

    for name_order in itertools.permutations(names):
        for hair_order in itertools.permutations(hair_colors):
            # Clue 3: Arnold is somewhere to the left of the person who has black hair.
            if name_order.index("Arnold") >= hair_order.index("black"):
                continue

            for sport_order in itertools.permutations(sports):
                # Clue 2: The person who has brown hair is the person who loves basketball.
                if hair_order.index("brown") != sport_order.index("basketball"):
                    continue

                for smoothie_order in itertools.permutations(smoothies):
                    # Clue 1: The Desert smoothie lover is Arnold.
                    if name_order[smoothie_order.index("desert")] != "Arnold":
                        continue

                    # Build rows for this valid solution
                    rows = []
                    for i, house in enumerate(houses):
                        row = [
                            str(house),
                            name_order[i],
                            hair_order[i],
                            sport_order[i],
                            smoothie_order[i],
                        ]
                        rows.append(row)
                    solutions_rows.append(rows)

    # Assuming a unique solution exists
    solution = solutions_rows[0] if solutions_rows else []

    output = {
        "solution": {
            "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
            "rows": solution,
        }
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()