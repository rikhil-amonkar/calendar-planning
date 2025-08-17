import itertools
import json

names_list = ['Peter', 'Eric', 'Alice', 'Arnold']
names_perms = [p for p in itertools.permutations(names_list) if p[1] != 'Eric' and p[2] != 'Arnold']

education_list = ['bachelor', 'high school', 'associate', 'master']
education_perms = [p for p in itertools.permutations(education_list) if p[3] != 'associate']

music_list = ['jazz', 'rock', 'pop', 'classical']
music_perms = [p for p in itertools.permutations(music_list) if p[1] == 'pop']

flower_list = ['lilies', 'carnations', 'daffodils', 'roses']
flower_perms = [p for p in itertools.permutations(flower_list) if p[0] != 'carnations' and p[3] != 'carnations']

color_list = ['green', 'red', 'yellow', 'white']
color_perms = list(itertools.permutations(color_list))

for names in names_perms:
    for educations in education_perms:
        for music in music_perms:
            for colors in color_perms:
                for flowers in flower_perms:
                    valid = True
                    
                    # Clue 1: bachelor → daffodils
                    for i in range(4):
                        if educations[i] == 'bachelor' and flowers[i] != 'daffodils':
                            valid = False
                            break
                    if not valid:
                        continue
                        
                    # Clue 3: master → Alice
                    alice_house = None
                    for i in range(4):
                        if educations[i] == 'master':
                            if names[i] != 'Alice':
                                valid = False
                                break
                            alice_house = i
                    if not valid:
                        continue
                        
                    # Clue 4: Alice's house directly left of classical
                    if alice_house is not None:
                        if alice_house + 1 >= 4 or music[alice_house + 1] != 'classical':
                            valid = False
                    if not valid:
                        continue
                        
                    # Clue 13: Arnold's color is yellow
                    arnold_house = None
                    for i in range(4):
                        if names[i] == 'Arnold':
                            arnold_house = i
                            if colors[i] != 'yellow':
                                valid = False
                                break
                    if not valid:
                        continue
                        
                    # Clue 7: yellow directly left of roses
                    if arnold_house is not None:
                        if arnold_house + 1 >= 4 or flowers[arnold_house + 1] != 'roses':
                            valid = False
                    if not valid:
                        continue
                        
                    # Clue 14: daffodils → yellow, and check Arnold has daffodils
                    for i in range(4):
                        if flowers[i] == 'daffodils':
                            if colors[i] != 'yellow' or names[i] != 'Arnold':
                                valid = False
                                break
                    if not valid:
                        continue
                        
                    # Clue 11 and 12: red is directly left of white and has rock
                    red_house = None
                    for i in range(4):
                        if colors[i] == 'red':
                            red_house = i
                            if i + 1 >= 4 or colors[i+1] != 'white':
                                valid = False
                                break
                            if music[i] != 'rock':
                                valid = False
                                break
                    if not valid:
                        continue
                        
                    # If all checks passed, build solution
                    solution_rows = []
                    for i in range(4):
                        house_num = i + 1
                        solution_rows.append([
                            str(house_num),
                            names[i],
                            educations[i],
                            music[i],
                            colors[i],
                            flowers[i]
                        ])
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
                            "rows": solution_rows
                        }
                    }
                    print(json.dumps(solution, indent=2))
                    exit()