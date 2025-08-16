#!/usr/bin/env python3
import json
import itertools

def solve():
    names_list = ["Peter", "Eric", "Alice", "Arnold"]
    educations_list = ["bachelor", "high school", "associate", "master"]
    music_list = ["jazz", "rock", "pop", "classical"]
    colors_list = ["green", "red", "yellow", "white"]
    flowers_list = ["lilies", "carnations", "daffodils", "roses"]

    # Iterate over all permutations for each category and check constraints.
    for names in itertools.permutations(names_list):
        # Clue 5: Eric is not in the second house (index 1)
        if names[1] == "Eric":
            continue
        # Clue 6: Arnold is not in the third house (index 2)
        if names[2] == "Arnold":
            continue

        for educations in itertools.permutations(educations_list):
            # Clue 3: The person with a master's degree is Alice.
            valid_master = True
            for i in range(4):
                if educations[i] == "master" and names[i] != "Alice":
                    valid_master = False
                    break
                if names[i] == "Alice" and educations[i] != "master":
                    valid_master = False
                    break
            if not valid_master:
                continue

            for music in itertools.permutations(music_list):
                # Clue 8: The person who loves pop music is in the second house.
                if music[1] != "pop":
                    continue
                # Clue 4: The person with a master's degree is directly left of the person who loves classical music.
                master_left_valid = True
                for i in range(3):
                    if educations[i] == "master" and music[i+1] != "classical":
                        master_left_valid = False
                        break
                if not master_left_valid:
                    continue

                for colors in itertools.permutations(colors_list):
                    # Clue 1 & 14: The bachelor loves daffodils and also loves yellow.
                    bachelor_color_ok = True
                    for i in range(4):
                        if educations[i] == "bachelor" and colors[i] != "yellow":
                            bachelor_color_ok = False
                            break
                        # Clue 13: Arnold is the person who loves yellow.
                        if names[i] == "Arnold" and colors[i] != "yellow":
                            bachelor_color_ok = False
                            break
                    if not bachelor_color_ok:
                        continue

                    # Clue 11: The person whose favorite color is red is directly left of the person who loves white.
                    redwhite = False
                    for i in range(3):
                        if colors[i] == "red" and colors[i+1] == "white":
                            redwhite = True
                            break
                    if not redwhite:
                        continue
                    # Additional: red cannot be in the last house because it must have a right neighbor.
                    if colors[3] == "red":
                        continue

                    for flowers in itertools.permutations(flowers_list):
                        # Clue 1: The person with a bachelor's degree is the person who loves a bouquet of daffodils.
                        bachelor_flower_ok = True
                        for i in range(4):
                            if educations[i] == "bachelor" and flowers[i] != "daffodils":
                                bachelor_flower_ok = False
                                break
                            if flowers[i] == "daffodils" and educations[i] != "bachelor":
                                bachelor_flower_ok = False
                                break
                        if not bachelor_flower_ok:
                            continue

                        # Clue 14 (equivalence): The person who loves daffodils is the person who loves yellow.
                        daffodils_yellow_ok = True
                        for i in range(4):
                            if flowers[i] == "daffodils" and colors[i] != "yellow":
                                daffodils_yellow_ok = False
                                break
                        if not daffodils_yellow_ok:
                            continue

                        # Clue 2: The person who loves a carnations arrangement is not in the first house.
                        if flowers[0] == "carnations":
                            continue
                        # Clue 10: The person who loves a carnations arrangement is not in the fourth house.
                        if flowers[3] == "carnations":
                            continue

                        # Clue 9: The person with an associate's degree is not in the fourth house.
                        if educations[3] == "associate":
                            continue

                        # Clue 7: The person who loves yellow is directly left of the person who loves the rose bouquet.
                        yellow_left_roses = True
                        for i in range(3):
                            if colors[i] == "yellow" and flowers[i+1] != "roses":
                                yellow_left_roses = False
                                break
                        if not yellow_left_roses:
                            continue

                        # Clue 12: The person whose favorite color is red is the person who loves rock music.
                        red_rock_ok = True
                        for i in range(4):
                            if colors[i] == "red" and music[i] != "rock":
                                red_rock_ok = False
                                break
                        if not red_rock_ok:
                            continue

                        # If we've passed all the constraints, we have a solution.
                        solution_rows = []
                        for i in range(4):
                            solution_rows.append([
                                str(i+1),
                                names[i],
                                educations[i],
                                music[i],
                                colors[i],
                                flowers[i]
                            ])
                        result = {
                            "solution": {
                                "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
                                "rows": solution_rows
                            }
                        }
                        print(json.dumps(result))
                        return

if __name__ == '__main__':
    solve()