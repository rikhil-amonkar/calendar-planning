import json
from itertools import permutations

def solve():
    houses = [1, 2, 3, 4]

    names_list = ["Eric", "Alice", "Peter", "Arnold"]
    hair_colors = ["blonde", "black", "red", "brown"]
    sports_list = ["swimming", "soccer", "basketball", "tennis"]

    def pos(arr, val):
        return arr.index(val)

    solutions = []

    # Iterate over all possible assignments
    for names in permutations(names_list):
        # Early pruning with fixed name-hair linkage will be applied later;
        # but we can still iterate all hair permutations with adjacency constraint
        for hairs in permutations(hair_colors):
            # Clue 7: Red hair is directly left of Black hair
            if not (pos(hairs, "red") + 1 == pos(hairs, "black")):
                continue

            for sports in permutations(sports_list):
                # Clue 1: Soccer is not in the second house
                if sports[1] == "soccer":
                    continue

                # Clue 4: Black hair person loves tennis
                if not (pos(hairs, "black") == pos(sports, "tennis")):
                    continue

                # Clue 2: Eric has blonde hair
                if not (pos(names, "Eric") == pos(hairs, "blonde")):
                    continue

                # Clue 3: Blonde hair is to the right of Basketball
                if not (pos(hairs, "blonde") > pos(sports, "basketball")):
                    continue

                # Clue 5: Arnold is somewhere to the left of the person with red hair
                if not (pos(names, "Arnold") < pos(hairs, "red")):
                    continue

                # Clue 6: Alice loves swimming
                if not (pos(names, "Alice") == pos(sports, "swimming")):
                    continue

                # All constraints satisfied; record solution
                solutions.append((names, hairs, sports))

    if not solutions:
        raise RuntimeError("No solution found")

    # Expect a unique solution; choose the first if multiple
    names, hairs, sports = solutions[0]

    output = {
        "solution": {
            "header": ["House", "Name", "HairColor", "FavoriteSport"],
            "rows": [
                [str(i + 1), names[i], hairs[i], sports[i]] for i in range(4)
            ]
        }
    }
    print(json.dumps(output, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    solve()