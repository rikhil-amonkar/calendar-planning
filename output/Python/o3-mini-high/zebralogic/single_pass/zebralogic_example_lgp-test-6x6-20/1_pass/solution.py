#!/usr/bin/env python3
import itertools
import json
import sys

def main():
    houses = 6
    names_list = ["Alice", "Peter", "Eric", "Bob", "Arnold", "Carol"]
    cigars_list = ["pall mall", "yellow monster", "dunhill", "blue master", "prince", "blends"]
    music_list = ["hip hop", "jazz", "country", "pop", "classical", "rock"]
    drinks_list = ["water", "milk", "boba tea", "tea", "root beer", "coffee"]
    mothers_list = ["Kailyn", "Penny", "Janelle", "Holly", "Sarah", "Aniya"]
    foods_list = ["soup", "pizza", "spaghetti", "stir fry", "stew", "grilled cheese"]

    for names in itertools.permutations(names_list):
        # Clue 2: Eric is not in the second house.
        if names.index("Eric") == 1:
            continue
        # Clue 5: Eric is directly left of Carol.
        if names.index("Eric") + 1 != names.index("Carol"):
            continue

        for mothers in itertools.permutations(mothers_list):
            # Clue 26: Eric's mother is Aniya.
            if mothers[names.index("Eric")] != "Aniya":
                continue
            # Clue 3: The person whose mother's name is Holly is somewhere to the right of Carol.
            if mothers.index("Holly") <= names.index("Carol"):
                continue
            # Clue 18: Arnold is somewhere to the right of the person whose mother's name is Kailyn.
            if names.index("Arnold") <= mothers.index("Kailyn"):
                continue

            for drinks in itertools.permutations(drinks_list):
                # Clue 9: The coffee drinker is Bob.
                if drinks[names.index("Bob")] != "coffee":
                    continue
                # Clue 14: Eric is the tea drinker.
                if drinks[names.index("Eric")] != "tea":
                    continue
                # Clue 25: The person who likes milk is the person whose mother's name is Janelle.
                if drinks[mothers.index("Janelle")] != "milk":
                    continue
                # Clue 12: The root beer lover is directly left of the person whose mother's name is Janelle.
                try:
                    idx_root = drinks.index("root beer")
                except ValueError:
                    continue
                if idx_root == houses - 1:
                    continue
                if not (mothers[idx_root + 1] == "Janelle" and drinks[idx_root + 1] == "milk"):
                    continue

                for music in itertools.permutations(music_list):
                    # Clue 8: The person who loves classical music is in the sixth house.
                    if music[5] != "classical":
                        continue
                    # Clue 7: Eric is the person who loves country music.
                    if music[names.index("Eric")] != "country":
                        continue
                    # Clue 6: The person who loves pop music is not in the third house.
                    if music[2] == "pop":
                        continue
                    # Clue 17: The person who loves hip-hop music is directly left of the person whose mother's name is Kailyn.
                    try:
                        idx_hiphop = music.index("hip hop")
                    except ValueError:
                        continue
                    if idx_hiphop == houses - 1:
                        continue
                    if mothers[idx_hiphop + 1] != "Kailyn":
                        continue
                    # Clue 21: The person whose mother's name is Sarah is directly left of the person who loves jazz music.
                    idx_sarah = mothers.index("Sarah")
                    if idx_sarah == houses - 1:
                        continue
                    if music[idx_sarah + 1] != "jazz":
                        continue
                    # Clue 22: The person who loves hip-hop music is directly left of the root beer lover.
                    if idx_hiphop == houses - 1 or drinks[idx_hiphop + 1] != "root beer":
                        continue

                    for cigars in itertools.permutations(cigars_list):
                        # Clue 24: The Dunhill smoker is not in the second house.
                        if cigars[1] == "dunhill":
                            continue
                        # Clue 10: The person who smokes many unique blends is Peter.
                        if cigars[names.index("Peter")] != "blends":
                            continue
                        # Clue 13: There are two houses between the person whose mother's name is Sarah and the person who smokes Yellow Monster.
                        if abs(cigars.index("yellow monster") - mothers.index("Sarah")) != 3:
                            continue

                        for foods in itertools.permutations(foods_list):
                            # Clue 1: Carol is directly left of the person who loves eating grilled cheese.
                            idx_carol = names.index("Carol")
                            if idx_carol == houses - 1 or foods[idx_carol + 1] != "grilled cheese":
                                continue
                            # Clue 4: The person who loves eating grilled cheese is somewhere to the right of the person who loves rock music.
                            if music.index("rock") >= foods.index("grilled cheese"):
                                continue
                            # Clue 11: The person who loves the stew is not in the fifth house.
                            if foods[4] == "stew":
                                continue
                            # Clue 16: The person who loves the soup is Bob.
                            if foods[names.index("Bob")] != "soup":
                                continue
                            # Clue 20: The person who loves the spaghetti is somewhere to the left of the person who smokes many unique blends.
                            if foods.index("spaghetti") >= names.index("Peter"):
                                continue
                            # Clue 23: The one who only drinks water is the person who loves the stew.
                            valid_water_stew = True
                            for i in range(houses):
                                if drinks[i] == "water" and foods[i] != "stew":
                                    valid_water_stew = False
                                    break
                                if foods[i] == "stew" and drinks[i] != "water":
                                    valid_water_stew = False
                                    break
                            if not valid_water_stew:
                                continue
                            # Clue 15: The person partial to Pall Mall is somewhere to the right of the person who loves stir fry.
                            if foods.index("stir fry") >= cigars.index("pall mall"):
                                continue
                            # Clue 19: The one who only drinks water is directly left of the person who smokes Blue Master.
                            try:
                                idx_water = drinks.index("water")
                            except ValueError:
                                continue
                            if idx_water == houses - 1 or cigars[idx_water + 1] != "blue master":
                                continue

                            # All constraints satisfied; build the solution.
                            solution_rows = []
                            for i in range(houses):
                                row = [str(i + 1), names[i], cigars[i], music[i], drinks[i], mothers[i], foods[i]]
                                solution_rows.append(row)
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"],
                                    "rows": solution_rows
                                }
                            }
                            print(json.dumps(solution))
                            return

if __name__ == "__main__":
    main()