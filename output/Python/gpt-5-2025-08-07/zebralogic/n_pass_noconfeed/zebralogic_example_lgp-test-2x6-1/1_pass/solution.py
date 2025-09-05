import json
from itertools import permutations

def solve_puzzle():
    # Input variables
    houses = [1, 2]  # left to right
    Names = ['Arnold', 'Eric']
    FavoriteSports = ['basketball', 'soccer']
    HairColors = ['brown', 'black']
    Heights = ['very short', 'short']
    Smoothies = ['desert', 'cherry']
    Flowers = ['daffodils', 'carnations']

    def idx(perm, value):
        return perm.index(value)

    solutions = []
    for names in permutations(Names):
        for sports in permutations(FavoriteSports):
            # Clue 1: The person who loves soccer is not in the second house.
            if idx(sports, 'soccer') == 1:
                continue

            for hairs in permutations(HairColors):
                for heights in permutations(Heights):
                    # Clue 3: The person who is very short is the person who has brown hair.
                    if idx(heights, 'very short') != idx(hairs, 'brown'):
                        continue

                    for smoothies in permutations(Smoothies):
                        # Clue 2: The Desert smoothie lover is directly left of the person who is very short.
                        if idx(smoothies, 'desert') + 1 != idx(heights, 'very short'):
                            continue

                        for flowers in permutations(Flowers):
                            # Clue 4: The person who loves a carnations arrangement is the Desert smoothie lover.
                            if idx(flowers, 'carnations') != idx(smoothies, 'desert'):
                                continue

                            # Clue 5: Eric and the person who has brown hair are next to each other.
                            if abs(idx(names, 'Eric') - idx(hairs, 'brown')) != 1:
                                continue

                            # If all constraints satisfied, we have a solution
                            solutions.append({
                                "names": names,
                                "sports": sports,
                                "hairs": hairs,
                                "heights": heights,
                                "smoothies": smoothies,
                                "flowers": flowers
                            })

    if not solutions:
        raise RuntimeError("No solution found")

    # Use the first found solution (should be unique)
    sol = solutions[0]
    header = ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"]
    rows = []
    for i, house in enumerate(houses):
        rows.append([
            str(house),
            sol["names"][i],
            sol["sports"][i],
            sol["hairs"][i],
            sol["heights"][i],
            sol["smoothies"][i],
            sol["flowers"][i]
        ])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))