import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2]  # left to right

    Names = ["Arnold", "Eric"]
    FavoriteSports = ["basketball", "soccer"]
    HairColors = ["brown", "black"]
    Heights = ["very short", "short"]
    Smoothies = ["desert", "cherry"]
    Flowers = ["daffodils", "carnations"]

    def idx_of(value, assignment):
        return assignment.index(value)

    solutions = []

    for name_perm in permutations(Names):
        for sport_perm in permutations(FavoriteSports):
            # Clue 1: The person who loves soccer is not in the second house.
            if sport_perm[1] == "soccer":
                continue

            for hair_perm in permutations(HairColors):
                for height_perm in permutations(Heights):
                    # Clue 2: Desert smoothie lover is directly left of the very short person.
                    # i_desert + 1 == i_very_short
                    # Clue 3: The person who is very short is the person who has brown hair.
                    if idx_of("very short", height_perm) != idx_of("brown", hair_perm):
                        continue

                    for smoothie_perm in permutations(Smoothies):
                        i_desert = idx_of("desert", smoothie_perm)
                        i_very_short = idx_of("very short", height_perm)
                        if i_desert + 1 != i_very_short:
                            continue

                        for flower_perm in permutations(Flowers):
                            # Clue 4: carnations lover is the Desert smoothie lover.
                            if idx_of("carnations", flower_perm) != i_desert:
                                continue

                            # Clue 5: Eric and the person who has brown hair are next to each other.
                            if abs(idx_of("Eric", name_perm) - idx_of("brown", hair_perm)) != 1:
                                continue

                            # Build solution rows
                            rows = []
                            for h in range(len(houses)):
                                row = [
                                    str(houses[h]),
                                    name_perm[h],
                                    sport_perm[h],
                                    hair_perm[h],
                                    height_perm[h],
                                    smoothie_perm[h],
                                    flower_perm[h],
                                ]
                                rows.append(row)

                            solutions.append(rows)

    # Assuming a unique solution, take the first
    if not solutions:
        raise ValueError("No solution found.")
    rows = solutions[0]

    output = {
        "solution": {
            "header": ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"],
            "rows": rows
        }
    }
    return output


if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))