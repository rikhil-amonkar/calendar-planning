import itertools
import json

def solve_puzzle():
    houses = [0, 1, 2, 3, 4]  # indices 0..4 correspond to houses 1..5

    Names = ["Bob", "Arnold", "Peter", "Alice", "Eric"]
    Drinks = ["milk", "root beer", "coffee", "tea", "water"]
    Colors = ["blue", "green", "white", "yellow", "red"]
    Flowers = ["daffodils", "roses", "lilies", "tulips", "carnations"]
    Hobbies = ["painting", "cooking", "photography", "gardening", "knitting"]

    solutions = []

    # Helper to check equivalence constraints between categories
    def eq_pair(arr1, val1, arr2, val2):
        # For all i, arr1[i]==val1 iff arr2[i]==val2
        for i in range(5):
            if (arr1[i] == val1) != (arr2[i] == val2):
                return False
        return True

    for colors in itertools.permutations(Colors):
        # Clue 15: White is in the second house (index 1)
        if colors[1] != "white":
            continue

        for drinks in itertools.permutations(Drinks):
            # Clue 13: Water is in the third house (index 2)
            if drinks[2] != "water":
                continue

            # Clue 3: Green = Coffee (equivalence)
            ok = True
            for i in range(5):
                if (colors[i] == "green") != (drinks[i] == "coffee"):
                    ok = False
                    break
            if not ok:
                continue

            # Now assign flowers
            for flowers in itertools.permutations(Flowers):
                # Clue 10: White = Roses (equivalence)
                valid = True
                for i in range(5):
                    if (colors[i] == "white") != (flowers[i] == "roses"):
                        valid = False
                        break
                if not valid:
                    continue

                # Clue 4: Green = Lilies (equivalence)
                for i in range(5):
                    if (colors[i] == "green") != (flowers[i] == "lilies"):
                        valid = False
                        break
                if not valid:
                    continue

                # Clue 14: Carnations = Root beer (equivalence)
                for i in range(5):
                    if (flowers[i] == "carnations") != (drinks[i] == "root beer"):
                        valid = False
                        break
                if not valid:
                    continue

                # Clue 11: One house between carnations and red
                idx_car = flowers.index("carnations")
                idx_red = colors.index("red")
                if abs(idx_car - idx_red) != 2:
                    continue

                # Clue 5: Blue is to the right of Daffodils
                idx_blue = colors.index("blue")
                idx_daf = flowers.index("daffodils")
                if not (idx_blue > idx_daf):
                    continue

                for hobbies in itertools.permutations(Hobbies):
                    # Clue 6: Cooking = Blue (equivalence)
                    valid = True
                    for i in range(5):
                        if (hobbies[i] == "cooking") != (colors[i] == "blue"):
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 2: Root beer = Gardening (equivalence)
                    for i in range(5):
                        if (drinks[i] == "root beer") != (hobbies[i] == "gardening"):
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 12: Cooking is somewhere to the left of Painting
                    if hobbies.index("cooking") >= hobbies.index("painting"):
                        continue

                    for names in itertools.permutations(Names):
                        # Clue 13 + 8: Water is in third house and the water drinker is Peter
                        if names[2] != "Peter":
                            continue
                        if names[drinks.index("water")] != "Peter":
                            continue

                        # Clue 1: Alice is not in the fourth house
                        if names[3] == "Alice":
                            continue

                        # Clue 9: Arnold = Photography
                        if hobbies[names.index("Arnold")] != "photography":
                            continue

                        # Clue 7: Eric is directly left of the Tea drinker
                        idx_eric = names.index("Eric")
                        idx_tea = drinks.index("tea")
                        if idx_eric != idx_tea - 1:
                            continue

                        # All constraints satisfied
                        rows = []
                        for i in range(5):
                            rows.append([
                                str(i + 1),
                                names[i],
                                drinks[i],
                                colors[i],
                                flowers[i],
                                hobbies[i],
                            ])
                        solutions.append(rows)

    # Take the first solution (should be unique)
    if not solutions:
        raise RuntimeError("No solution found")

    solution_rows = solutions[0]
    result = {
        "solution": {
            "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
            "rows": solution_rows
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))