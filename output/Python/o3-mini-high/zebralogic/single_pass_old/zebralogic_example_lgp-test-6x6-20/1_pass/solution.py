#!/usr/bin/env python3
import itertools
import json
import sys

def solve():
    # Define the possible values for each category.
    names_options    = ["Alice", "Peter", "Eric", "Bob", "Arnold", "Carol"]
    cigars_options   = ["pall mall", "yellow monster", "dunhill", "blue master", "prince", "blends"]
    music_options    = ["hip hop", "jazz", "country", "pop", "classical", "rock"]
    drinks_options   = ["water", "milk", "boba tea", "tea", "root beer", "coffee"]
    mothers_options  = ["Kailyn", "Penny", "Janelle", "Holly", "Sarah", "Aniya"]
    lunches_options  = ["soup", "pizza", "spaghetti", "stir fry", "stew", "grilled cheese"]
    
    # Loop over all assignments for Names.
    for names in itertools.permutations(names_options):
        # Clue 2: Eric is not in the second house.
        if names[1] == "Eric":
            continue
        # Clue 5: Eric is directly left of Carol.
        try:
            e_index = names.index("Eric")
        except ValueError:
            continue
        if e_index == 5 or names[e_index+1] != "Carol":
            continue

        # Loop over all assignments for Mothers' names.
        for mothers in itertools.permutations(mothers_options):
            # Clue 26: Eric's mother's name is Aniya.
            if mothers[names.index("Eric")] != "Aniya":
                continue
            # Clue 3: The person whose mother's name is Holly is somewhere to the right of Carol.
            if mothers.index("Holly") <= names.index("Carol"):
                continue
            # Clue 18: Arnold is somewhere to the right of the person whose mother's name is Kailyn.
            if mothers.index("Kailyn") >= names.index("Arnold"):
                continue

            # Loop over all assignments for Music.
            for musics in itertools.permutations(music_options):
                # Clue 8: The person who loves classical music is in the sixth house.
                if musics[5] != "classical":
                    continue
                # Clue 7: Eric is the person who loves country music.
                if musics[names.index("Eric")] != "country":
                    continue
                # Clue 6: The person who loves pop music is not in the third house.
                if musics[2] == "pop":
                    continue
                # Clue 17: The person who loves hip-hop music is directly left of the person whose mother's name is Kailyn.
                hip_index = musics.index("hip hop")
                if hip_index == 5 or mothers[hip_index+1] != "Kailyn":
                    continue
                # Clue 21: The person whose mother's name is Sarah is directly left of the person who loves jazz music.
                sarah_index = mothers.index("Sarah")
                if sarah_index == 5 or musics[sarah_index+1] != "jazz":
                    continue

                # Loop over all assignments for Drinks.
                for drinks in itertools.permutations(drinks_options):
                    # Clue 9: The coffee drinker is Bob.
                    if drinks[names.index("Bob")] != "coffee":
                        continue
                    # Clue 14: Eric is the tea drinker.
                    if drinks[names.index("Eric")] != "tea":
                        continue
                    # Clue 25: The person who likes milk is the person whose mother's name is Janelle.
                    milk_index = drinks.index("milk")
                    if mothers[milk_index] != "Janelle":
                        continue
                    # Clue 22: The person who loves hip-hop music is directly left of the root beer lover.
                    if hip_index == 5 or drinks[hip_index+1] != "root beer":
                        continue
                    # Clue 12: The root beer lover is directly left of the person whose mother's name is Janelle.
                    root_beer_index = drinks.index("root beer")
                    if root_beer_index == 5 or mothers[root_beer_index+1] != "Janelle":
                        continue

                    # Loop over all assignments for Cigars.
                    for cigars in itertools.permutations(cigars_options):
                        # Clue 10: The person who smokes many unique blends is Peter.
                        try:
                            index_blends = cigars.index("blends")
                        except ValueError:
                            continue
                        if names[index_blends] != "Peter":
                            continue
                        # Clue 24: The Dunhill smoker is not in the second house.
                        if cigars[1] == "dunhill":
                            continue
                        # Clue 19: The one who only drinks water is directly left of the person who smokes Blue Master.
                        water_index = drinks.index("water")
                        if water_index == 5 or cigars[water_index+1] != "blue master":
                            continue
                        # Clue 13: There are two houses between the person whose mother's name is Sarah and the person who smokes Yellow Monster.
                        if abs(mothers.index("Sarah") - cigars.index("yellow monster")) != 3:
                            continue

                        # Loop over all assignments for Lunch.
                        for lunches in itertools.permutations(lunches_options):
                            # Clue 1: Carol is directly left of the person who loves eating grilled cheese.
                            c_index = names.index("Carol")
                            if c_index == 5 or lunches[c_index+1] != "grilled cheese":
                                continue
                            # Clue 4: The person who loves eating grilled cheese is somewhere to the right of the person who loves rock music.
                            grilled_index = lunches.index("grilled cheese")
                            rock_index = musics.index("rock")
                            if not (grilled_index > rock_index):
                                continue
                            # Clue 11 & 23: The one who only drinks water is the person who loves the stew,
                            # and the stew-lover is not in the fifth house.
                            water_drinker = drinks.index("water")
                            if water_drinker == 4 or lunches[water_drinker] != "stew":
                                continue
                            # Clue 16: The person who loves the soup is Bob.
                            if lunches[names.index("Bob")] != "soup":
                                continue
                            # Clue 20: The person who loves spaghetti is somewhere to the left of the person who smokes many unique blends.
                            if lunches.index("spaghetti") >= index_blends:
                                continue
                            # Clue 15: The person partial to Pall Mall is somewhere to the right of the person who loves stir fry.
                            if lunches.index("stir fry") >= cigars.index("pall mall"):
                                continue

                            # All constraints satisfied; build the solution.
                            header = ["House", "Name", "favorite cigar", "favorite music", "favorite drink", "mothers' names", "lunch"]
                            rows = []
                            for i in range(6):
                                rows.append([
                                    str(i+1),
                                    names[i],
                                    cigars[i],
                                    musics[i],
                                    drinks[i],
                                    mothers[i],
                                    lunches[i]
                                ])
                            solution = {"solution": {"header": header, "rows": rows}}
                            print(json.dumps(solution, indent=2))
                            return

if __name__=="__main__":
    solve()