import itertools
import json

def main():
    names_list = ['Peter', 'Eric', 'Alice', 'Arnold']
    education_list = ['bachelor', 'high school', 'associate', 'master']
    music_list = ['jazz', 'rock', 'pop', 'classical']
    color_list = ['green', 'red', 'yellow', 'white']
    flower_list = ['lilies', 'carnations', 'daffodils', 'roses']

    for names in itertools.permutations(names_list):
        # Check Eric not in second house (index 1) and Arnold not in third (index 2)
        if names[1] == 'Eric' or names[2] == 'Arnold':
            continue

        for educations in itertools.permutations(education_list):
            valid_edu = True
            master_pos = None
            bachelor_pos = None
            for i in range(4):
                if educations[i] == 'master':
                    if names[i] != 'Alice':
                        valid_edu = False
                        break
                    master_pos = i
                if educations[i] == 'bachelor':
                    if names[i] != 'Arnold':
                        valid_edu = False
                        break
                    bachelor_pos = i
            if not valid_edu:
                continue
            if master_pos == 3:
                continue  # Master can't be in house 4 (no house to the right)
            if educations[3] == 'associate':
                continue  # Clue 9: associate not in fourth house

            for musics in itertools.permutations(music_list):
                if musics[1] != 'pop':
                    continue  # Clue 8: pop in second house

                if master_pos is not None:
                    if master_pos + 1 >= 4 or musics[master_pos + 1] != 'classical':
                        continue  # Clue 4: master left of classical

                for colors in itertools.permutations(color_list):
                    # Check Arnold's color is yellow (Clue 13)
                    arnold_color = None
                    for i in range(4):
                        if names[i] == 'Arnold':
                            arnold_color = colors[i]
                            break
                    if arnold_color != 'yellow':
                        continue

                    # Check Clue 11: red directly left of white
                    red_index = -1
                    try:
                        red_index = colors.index('red')
                    except ValueError:
                        pass
                    if red_index != -1:
                        if red_index + 1 >= 4 or colors[red_index + 1] != 'white':
                            continue

                    # Check Clue 12: red's music is rock
                    if red_index != -1 and musics[red_index] != 'rock':
                        continue

                    for flowers in itertools.permutations(flower_list):
                        # Check Clue 2 and 10: carnations not in first or fourth
                        try:
                            carnation_pos = flowers.index('carnations')
                        except ValueError:
                            carnation_pos = -1
                        if carnation_pos in (0, 3):
                            continue

                        # Check Clue 1: bachelor's flower is daffodils
                        if flowers[bachelor_pos] != 'daffodils':
                            continue

                        # Check Clue 14: daffodils has yellow color
                        try:
                            daffodil_pos = flowers.index('daffodils')
                        except ValueError:
                            daffodil_pos = -1
                        if daffodil_pos != -1 and colors[daffodil_pos] != 'yellow':
                            continue

                        # Check Clue 7: yellow's next flower is roses
                        yellow_index = colors.index('yellow')
                        if yellow_index + 1 >= 4 or flowers[yellow_index + 1] != 'roses':
                            continue

                        # All constraints passed, build the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
                                "rows": [
                                    [str(i + 1), names[i], educations[i], musics[i], colors[i], flowers[i]]
                                    for i in range(4)
                                ]
                            }
                        }
                        print(json.dumps(solution, indent=2))
                        return

if __name__ == "__main__":
    main()