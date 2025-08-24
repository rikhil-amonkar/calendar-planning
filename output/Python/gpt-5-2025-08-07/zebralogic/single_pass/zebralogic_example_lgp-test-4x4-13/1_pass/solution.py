import itertools
import json

def solve_puzzle():
    # Attributes
    houses = [1, 2, 3, 4]
    Names = ["Alice", "Peter", "Arnold", "Eric"]
    Cigars = ["prince", "dunhill", "blue master", "pall mall"]
    Sports = ["swimming", "basketball", "soccer", "tennis"]
    Drinks = ["coffee", "water", "milk", "tea"]

    # Helper to ensure a value maps to the same house across attributes
    def same_house(value, perm_a, value_b, perm_b):
        return perm_a.index(value) == perm_b.index(value_b)

    solution = None

    # Generate permutations with early pruning based on fixed-position clues
    for names in itertools.permutations(Names):
        # 1. Peter is in the fourth house.
        if names[3] != "Peter":
            continue

        for sports in itertools.permutations(Sports):
            # 8. The person who loves basketball is in the third house.
            if sports[2] != "basketball":
                continue

            for drinks in itertools.permutations(Drinks):
                # 6. There are two houses between the one who only drinks water and Peter.
                # Peter is at house 4 (index 3), so water must be at house 1 (index 0).
                if drinks[0] != "water":
                    continue

                # 2. The tea drinker is the person who loves basketball.
                if drinks.index("tea") != sports.index("basketball"):
                    continue

                # 4. The person who loves basketball is Eric.
                if names[sports.index("basketball")] != "Eric":
                    continue

                # 6 (redundant check): water and Peter have distance 3
                if abs(drinks.index("water") - names.index("Peter")) != 3:
                    continue

                for cigars in itertools.permutations(Cigars):
                    # 10. Peter is the person partial to Pall Mall.
                    if cigars[names.index("Peter")] != "pall mall":
                        continue

                    # 3. Arnold is the person who smokes Blue Master.
                    if cigars[names.index("Arnold")] != "blue master":
                        continue

                    # 7. The coffee drinker is Arnold.
                    if drinks[names.index("Arnold")] != "coffee":
                        continue

                    # 5. The person who loves tennis is the person who smokes Blue Master.
                    if sports[cigars.index("blue master")] != "tennis":
                        continue

                    # 9. The Prince smoker is the person who loves soccer.
                    if sports[cigars.index("prince")] != "soccer":
                        continue

                    # All constraints satisfied; build the solution
                    rows = []
                    for i in range(4):
                        rows.append([
                            str(houses[i]),
                            names[i],
                            cigars[i],
                            sports[i],
                            drinks[i],
                        ])

                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
                            "rows": rows
                        }
                    }
                    return solution

    return {"solution": {"header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"], "rows": []}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))