#!/usr/bin/env python3
import itertools
import json

def main():
    NAMES = ["Alice", "Carol", "Eric", "Peter", "Bob", "Arnold"]
    PHONES = ["huawei p50", "google pixel 6", "xiaomi mi 11", "iphone 13", "samsung galaxy s21", "oneplus 9"]
    CIGARS = ["dunhill", "pall mall", "blends", "blue master", "prince", "yellow monster"]
    FLOWERS = ["daffodils", "carnations", "roses", "tulips", "lilies", "iris"]
    COLORS = ["yellow", "red", "green", "blue", "white", "purple"]
    SPORTS = ["soccer", "tennis", "basketball", "volleyball", "swimming", "baseball"]

    # We assign each attribute as a permutation of the six houses (index 0 to 5).
    for names_perm in itertools.permutations(NAMES):
        # Clue 18: Alice is in the first house.
        if names_perm[0] != "Alice":
            continue

        for phones_perm in itertools.permutations(PHONES):
            # Clue 1: OnePlus 9 is in the second house.
            if phones_perm[1] != "oneplus 9":
                continue
            # Clue 2: Xiaomi Mi 11 is somewhere to the left of Huawei P50.
            if phones_perm.index("xiaomi mi 11") >= phones_perm.index("huawei p50"):
                continue
            # Clue 7: Eric is somewhere to the right of the person who uses a Samsung Galaxy S21.
            pos_samsung = phones_perm.index("samsung galaxy s21")
            pos_eric = names_perm.index("Eric")
            if not (pos_samsung < pos_eric):
                continue

            for cigars_perm in itertools.permutations(CIGARS):
                # Clue 15: The Dunhill smoker is Peter.
                idx_dunhill = cigars_perm.index("dunhill")
                if names_perm[idx_dunhill] != "Peter":
                    continue
                # Clue 23: Eric is the person who smokes many unique blends.
                if cigars_perm[names_perm.index("Eric")] != "blends":
                    continue

                for flowers_perm in itertools.permutations(FLOWERS):
                    # Clue 3: Carol is the person who loves a carnations arrangement.
                    if flowers_perm[names_perm.index("Carol")] != "carnations":
                        continue
                    # Clue 13: The person who uses a OnePlus 9 and the person who loves roses are next to each other.
                    pos_oneplus = phones_perm.index("oneplus 9")
                    pos_roses = flowers_perm.index("roses")
                    if abs(pos_oneplus - pos_roses) != 1:
                        continue
                    # Clue 14: The person who loves iris is somewhere to the left of Eric.
                    pos_iris = flowers_perm.index("iris")
                    if not (pos_iris < names_perm.index("Eric")):
                        continue
                    # Clue 8: There are two houses between Carol and the person who loves daffodils.
                    pos_carol = names_perm.index("Carol")
                    pos_daffodils = flowers_perm.index("daffodils")
                    if abs(pos_carol - pos_daffodils) != 3:
                        continue
                    # Clue 17: The person who loves tulips is Bob.
                    if flowers_perm[names_perm.index("Bob")] != "tulips":
                        continue

                    for colors_perm in itertools.permutations(COLORS):
                        # Clue 6: The person who loves yellow and the person who loves blue are next to each other.
                        pos_yellow = colors_perm.index("yellow")
                        pos_blue = colors_perm.index("blue")
                        if abs(pos_yellow - pos_blue) != 1:
                            continue
                        # Clue 16: The person who loves blue is Peter.
                        if colors_perm[names_perm.index("Peter")] != "blue":
                            continue
                        # Clue 12: The person who uses a Huawei P50 is directly left of the person who loves white.
                        pos_huawei = phones_perm.index("huawei p50")
                        if pos_huawei == 5 or colors_perm[pos_huawei + 1] != "white":
                            continue
                        # Clue 4: The person who loves purple is directly left of the person who smokes Pall Mall.
                        pos_purple = colors_perm.index("purple")
                        pos_pall_mall = cigars_perm.index("pall mall")
                        if pos_pall_mall != pos_purple + 1:
                            continue
                        # Clue 5: The person whose favorite color is green is the person who smokes Blue Master.
                        if colors_perm.index("green") != cigars_perm.index("blue master"):
                            continue

                        for sports_perm in itertools.permutations(SPORTS):
                            # Clue 24: The person who loves volleyball is the person who uses an iPhone 13.
                            if phones_perm[sports_perm.index("volleyball")] != "iphone 13":
                                continue
                            # Clue 10: The Dunhill smoker is the person who loves volleyball.
                            if sports_perm[idx_dunhill] != "volleyball":
                                continue
                            # Clue 9: The Prince smoker is the person who loves basketball.
                            if sports_perm[cigars_perm.index("prince")] != "basketball":
                                continue
                            # Clue 11: The person who loves swimming is the person who uses a Google Pixel 6.
                            if phones_perm[sports_perm.index("swimming")] != "google pixel 6":
                                continue
                            # Clue 19: The person who loves baseball is directly left of the person who smokes Blue Master.
                            pos_baseball = sports_perm.index("baseball")
                            if pos_baseball == 5 or cigars_perm[pos_baseball + 1] != "blue master":
                                continue
                            # Clue 20: The person who uses a Google Pixel 6 is somewhere to the right of the person who smokes blends.
                            if phones_perm.index("google pixel 6") <= cigars_perm.index("blends"):
                                continue
                            # Clue 21: The person who loves soccer is Carol.
                            if sports_perm[names_perm.index("Carol")] != "soccer":
                                continue
                            # Clue 22: The person who loves carnations is directly left of the person who smokes blends.
                            pos_carnations = flowers_perm.index("carnations")
                            if pos_carnations == 5 or cigars_perm[pos_carnations + 1] != "blends":
                                continue

                            # If all constraints are satisfied, build the solution.
                            solution_rows = []
                            for i in range(6):
                                house_number = str(i+1)
                                row = [house_number, names_perm[i], phones_perm[i], cigars_perm[i],
                                       flowers_perm[i], colors_perm[i], sports_perm[i]]
                                solution_rows.append(row)
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"],
                                    "rows": solution_rows
                                }
                            }
                            print(json.dumps(result, indent=2))
                            return

if __name__ == '__main__':
    main()