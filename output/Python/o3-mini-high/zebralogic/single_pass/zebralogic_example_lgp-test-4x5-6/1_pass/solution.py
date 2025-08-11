#!/usr/bin/env python3
import itertools
import json

def valid_solution(names, educations, music, colors, flowers):
    # Constraint 1: The person with a bachelor's degree is the person who loves a bouquet of daffodils.
    for i in range(4):
        if educations[i] == "bachelor" and flowers[i] != "daffodils":
            return False
        if flowers[i] == "daffodils" and educations[i] != "bachelor":
            return False

    # Constraint 2: The person who loves a carnations arrangement is not in the first house.
    if flowers[0] == "carnations":
        return False

    # Constraint 3: The person with a master's degree is Alice.
    for i in range(4):
        if educations[i] == "master" and names[i] != "Alice":
            return False
        if names[i] == "Alice" and educations[i] != "master":
            return False

    # Constraint 4: The person with a master's degree is directly left of the person who loves classical music.
    for i in range(4):
        if educations[i] == "master":
            if i == 3 or music[i+1] != "classical":
                return False

    # Constraint 5: Eric is not in the second house.
    if names[1] == "Eric":
        return False

    # Constraint 6: Arnold is not in the third house.
    if names[2] == "Arnold":
        return False

    # Constraint 7: The person who loves yellow is directly left of the person who loves the rose bouquet.
    for i in range(4):
        if colors[i] == "yellow":
            if i == 3 or flowers[i+1] != "roses":
                return False
            break

    # Constraint 8: The person who loves pop music is in the second house.
    if music[1] != "pop":
        return False

    # Constraint 9: The person with an associate's degree is not in the fourth house.
    if educations[3] == "associate":
        return False

    # Constraint 10: The person who loves a carnations arrangement is not in the fourth house.
    if flowers[3] == "carnations":
        return False

    # Constraint 11: The person whose favorite color is red is directly left of the person who loves white.
    for i in range(4):
        if colors[i] == "red":
            if i == 3 or colors[i+1] != "white":
                return False
            break

    # Constraint 12: The person whose favorite color is red is the person who loves rock music.
    for i in range(4):
        if colors[i] == "red" and music[i] != "rock":
            return False
        if music[i] == "rock" and colors[i] != "red":
            return False

    # Constraint 13: Arnold is the person who loves yellow.
    for i in range(4):
        if names[i] == "Arnold" and colors[i] != "yellow":
            return False

    # Constraint 14: The person who loves a bouquet of daffodils is the person who loves yellow.
    for i in range(4):
        if flowers[i] == "daffodils" and colors[i] != "yellow":
            return False
        if colors[i] == "yellow" and flowers[i] != "daffodils":
            return False

    return True

def main():
    names_list = ["Peter", "Eric", "Alice", "Arnold"]
    education_list = ["bachelor", "high school", "associate", "master"]
    music_list = ["jazz", "rock", "pop", "classical"]
    color_list = ["green", "red", "yellow", "white"]
    flower_list = ["lilies", "carnations", "daffodils", "roses"]

    for names_perm in itertools.permutations(names_list):
        for education_perm in itertools.permutations(education_list):
            for music_perm in itertools.permutations(music_list):
                for color_perm in itertools.permutations(color_list):
                    for flower_perm in itertools.permutations(flower_list):
                        if valid_solution(names_perm, education_perm, music_perm, color_perm, flower_perm):
                            header = ["House", "Name", "Education", "Favorite music", "Favorite color", "Favorite flower"]
                            rows = []
                            for i in range(4):
                                row = [str(i+1), names_perm[i], education_perm[i], music_perm[i], color_perm[i], flower_perm[i]]
                                rows.append(row)
                            solution = {"solution": {"header": header, "rows": rows}}
                            print(json.dumps(solution, indent=2))
                            return

if __name__ == "__main__":
    main()