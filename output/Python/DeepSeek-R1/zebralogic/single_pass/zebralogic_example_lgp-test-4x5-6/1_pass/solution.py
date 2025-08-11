import itertools
import json

def main():
    names = ['Peter', 'Eric', 'Alice', 'Arnold']
    educations = ['bachelor', 'high school', 'associate', 'master']
    musics = ['jazz', 'rock', 'pop', 'classical']
    colors = ['green', 'red', 'yellow', 'white']
    flowers = ['lilies', 'carnations', 'daffodils', 'roses']

    for name_assign in itertools.permutations(names):
        if name_assign[1] == 'Eric':  # Clue 5: Eric not in second house (index1)
            continue
        if name_assign[2] == 'Arnold':  # Clue 6: Arnold not in third house (index2)
            continue

        for edu_assign in itertools.permutations(educations):
            try:
                idx_master = edu_assign.index('master')
            except ValueError:
                continue
            if name_assign[idx_master] != 'Alice':  # Clue 3: master's degree is Alice
                continue
            if edu_assign[3] == 'associate':  # Clue 9: associate not in fourth house (index3)
                continue

            for music_assign in itertools.permutations(musics):
                if music_assign[1] != 'pop':  # Clue 8: pop music in second house (index1)
                    continue
                if idx_master < 3:  # Clue 4: master directly left of classical
                    if music_assign[idx_master+1] != 'classical':
                        continue
                else:
                    continue

                for color_assign in itertools.permutations(colors):
                    try:
                        idx_arnold = name_assign.index('Arnold')
                    except ValueError:
                        continue
                    if color_assign[idx_arnold] != 'yellow':  # Clue 13: Arnold loves yellow
                        continue
                    found_red_white = False
                    for i in range(3):  # Clue 11: red directly left of white
                        if color_assign[i] == 'red' and color_assign[i+1] == 'white':
                            found_red_white = True
                            break
                    if not found_red_white:
                        continue

                    for flower_assign in itertools.permutations(flowers):
                        try:
                            idx_bachelor = edu_assign.index('bachelor')
                        except ValueError:
                            continue
                        if flower_assign[idx_bachelor] != 'daffodils':  # Clue 1: bachelor loves daffodils
                            continue
                        if flower_assign[0] == 'carnations':  # Clue 2: carnations not in first house (index0)
                            continue
                        if idx_arnold < 3:  # Clue 7: yellow directly left of roses
                            if flower_assign[idx_arnold+1] != 'roses':
                                continue
                        else:
                            continue
                        if flower_assign[3] == 'carnations':  # Clue 10: carnations not in fourth house (index3)
                            continue
                        if idx_bachelor != idx_arnold:  # Clue 14: daffodils and yellow same house
                            continue
                        try:
                            idx_red = color_assign.index('red')
                        except ValueError:
                            continue
                        if music_assign[idx_red] != 'rock':  # Clue 12: red color loves rock music
                            continue

                        solution = []
                        for i in range(4):
                            solution.append({
                                'House': str(i+1),
                                'Name': name_assign[i],
                                'Education': edu_assign[i],
                                'Music': music_assign[i],
                                'Color': color_assign[i],
                                'Flower': flower_assign[i]
                            })

                        header = ['House', 'Name', 'Education', 'Music', 'Color', 'Flower']
                        rows = []
                        for house in solution:
                            rows.append([
                                house['House'],
                                house['Name'],
                                house['Education'],
                                house['Music'],
                                house['Color'],
                                house['Flower']
                            ])

                        result = {
                            "solution": {
                                "header": header,
                                "rows": rows
                            }
                        }
                        print(json.dumps(result))
                        return

    print(json.dumps({"error": "No solution found"}))

if __name__ == '__main__':
    main()