import json
import itertools

def solve_puzzle():
    # Input variables
    houses = [1, 2, 3, 4]  # left (1) to right (4)
    names = ["Eric", "Alice", "Peter", "Arnold"]
    hair_colors = ["blonde", "black", "red", "brown"]
    sports = ["swimming", "soccer", "basketball", "tennis"]

    solutions = []

    # Iterate over possible assignments of hair colors to houses
    for hair_perm in itertools.permutations(hair_colors):
        # Build helper index map: hair -> house index (0-based)
        hair_idx = {color: hair_perm.index(color) for color in hair_colors}

        # Constraint 7: red is directly left of black
        if not (hair_idx["red"] + 1 == hair_idx["black"]):
            continue

        # Constraint 5 implies red cannot be in the first house (since Arnold must be left of red)
        if hair_idx["red"] == 0:
            continue

        # Iterate over possible assignments of names to houses
        for name_perm in itertools.permutations(names):
            name_idx = {name: name_perm.index(name) for name in names}

            # Constraint 2: Eric has blonde hair
            if not (name_idx["Eric"] == hair_idx["blonde"]):
                continue

            # Constraint 5: Arnold is somewhere to the left of red hair
            if not (name_idx["Arnold"] < hair_idx["red"]):
                continue

            # Iterate over possible assignments of sports to houses
            for sport_perm in itertools.permutations(sports):
                sport_idx = {sport: sport_perm.index(sport) for sport in sports}

                # Constraint 1: The person who loves soccer is not in the second house (house index 1)
                if sport_idx["soccer"] == 1:
                    continue

                # Constraint 4: The person with black hair loves tennis
                if not (hair_idx["black"] == sport_idx["tennis"]):
                    continue

                # Constraint 6: Alice loves swimming
                if not (name_idx["Alice"] == sport_idx["swimming"]):
                    continue

                # Constraint 3: Blonde hair is to the right of basketball
                if not (hair_idx["blonde"] > sport_idx["basketball"]):
                    continue

                # All constraints satisfied; record solution
                rows = []
                for i in range(4):
                    rows.append([
                        str(houses[i]),
                        name_perm[i],
                        hair_perm[i],
                        sport_perm[i]
                    ])
                solutions.append({
                    "solution": {
                        "header": ["House", "Name", "HairColor", "FavoriteSport"],
                        "rows": rows
                    }
                })

    # Ensure at least one solution found
    if not solutions:
        raise RuntimeError("No solution found for the given puzzle constraints.")

    # If multiple solutions exist, we can choose the first; typically puzzles are unique
    return solutions[0]

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))