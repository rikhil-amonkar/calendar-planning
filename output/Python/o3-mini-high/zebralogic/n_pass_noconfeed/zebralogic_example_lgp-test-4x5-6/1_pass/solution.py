import itertools
import json

def main():
    names = ["Peter", "Eric", "Alice", "Arnold"]
    educations = ["bachelor", "high school", "associate", "master"]
    music_genres = ["jazz", "rock", "pop", "classical"]
    colors = ["green", "red", "yellow", "white"]
    flowers = ["lilies", "carnations", "daffodils", "roses"]

    houses_idx = range(4)  # indices 0,1,2,3 corresponding to houses 1,2,3,4

    # Iterate over all permutations of attributes and check constraints
    for name_perm in itertools.permutations(names):
        # Constraint 5: Eric is not in the second house (index 1)
        if name_perm[1] == "Eric":
            continue
        # Constraint 6: Arnold is not in the third house (index 2)
        if name_perm[2] == "Arnold":
            continue

        for edu_perm in itertools.permutations(educations):
            # Constraint 3: The person with a master's degree is Alice.
            valid_edu = True
            for i in houses_idx:
                if edu_perm[i] == "master" and name_perm[i] != "Alice":
                    valid_edu = False
                    break
                if name_perm[i] == "Alice" and edu_perm[i] != "master":
                    valid_edu = False
                    break
            if not valid_edu:
                continue
            # Constraint 9: The person with an associate's degree is not in the fourth house.
            if edu_perm[3] == "associate":
                continue

            for music_perm in itertools.permutations(music_genres):
                # Constraint 8: The person who loves pop music is in the second house.
                if music_perm[1] != "pop":
                    continue
                # Constraint 4: The person with a master's degree is directly left of the person who loves classical music.
                # Find the index of the master (Alice)
                try:
                    master_index = edu_perm.index("master")
                except ValueError:
                    continue
                if master_index == 3 or music_perm[master_index + 1] != "classical":
                    continue

                for color_perm in itertools.permutations(colors):
                    # Constraint 13: Arnold is the person who loves yellow.
                    color_valid = True
                    for i in houses_idx:
                        if name_perm[i] == "Arnold" and color_perm[i] != "yellow":
                            color_valid = False
                            break
                    if not color_valid:
                        continue

                    # Constraint 12: The person whose favorite color is red is the person who loves rock music.
                    for i in houses_idx:
                        if color_perm[i] == "red" and music_perm[i] != "rock":
                            color_valid = False
                            break
                    if not color_valid:
                        continue

                    # Constraint 11: The person whose favorite color is red is directly left of the person who loves white.
                    try:
                        red_index = color_perm.index("red")
                    except ValueError:
                        continue
                    if red_index == 3 or color_perm[red_index + 1] != "white":
                        continue

                    for flower_perm in itertools.permutations(flowers):
                        # Constraint 1: The person with a bachelor's degree is the person who loves a bouquet of daffodils.
                        valid_flowers = True
                        for i in houses_idx:
                            if edu_perm[i] == "bachelor" and flower_perm[i] != "daffodils":
                                valid_flowers = False
                                break
                            if flower_perm[i] == "daffodils" and edu_perm[i] != "bachelor":
                                valid_flowers = False
                                break
                        if not valid_flowers:
                            continue

                        # Constraint 14: The person who loves a bouquet of daffodils is the person who loves yellow.
                        daffodil_yellow = True
                        for i in houses_idx:
                            if flower_perm[i] == "daffodils" and color_perm[i] != "yellow":
                                daffodil_yellow = False
                                break
                            if color_perm[i] == "yellow" and flower_perm[i] != "daffodils":
                                daffodil_yellow = False
                                break
                        if not daffodil_yellow:
                            continue

                        # Constraint 2: The person who loves a carnations arrangement is not in the first house.
                        if flower_perm[0] == "carnations":
                            continue
                        # Constraint 10: The person who loves a carnations arrangement is not in the fourth house.
                        if flower_perm[3] == "carnations":
                            continue

                        # Constraint 7: The person who loves yellow is directly left of the person who loves the rose bouquet.
                        try:
                            yellow_index = color_perm.index("yellow")
                        except ValueError:
                            continue
                        if yellow_index == 3 or flower_perm[yellow_index + 1] != "roses":
                            continue

                        # If we reach here, all constraints are satisfied.
                        solution = []
                        for i in houses_idx:
                            solution.append([
                                str(i + 1),
                                name_perm[i],
                                edu_perm[i],
                                music_perm[i],
                                color_perm[i],
                                flower_perm[i]
                            ])
                        output = {
                            "solution": {
                                "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
                                "rows": solution
                            }
                        }
                        print(json.dumps(output))
                        return

if __name__ == "__main__":
    main()