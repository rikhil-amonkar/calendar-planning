import itertools
import json

names = ['Peter', 'Arnold', 'Eric', 'Alice']
flowers = ['daffodils', 'carnations', 'roses', 'lilies']
heights = ['very short', 'short', 'tall', 'average']
mothers = ['Janelle', 'Kailyn', 'Holly', 'Aniya']
occupations = ['engineer', 'doctor', 'teacher', 'artist']
sports = ['swimming', 'basketball', 'tennis', 'soccer']

solution_found = False

for name_perm in itertools.permutations(names):
    arnold_idx = name_perm.index('Arnold')
    eric_idx = name_perm.index('Eric')
    peter_idx = name_perm.index('Peter')
    alice_idx = name_perm.index('Alice')

    for flower_perm in itertools.permutations(flowers):
        if flower_perm[eric_idx] != 'roses':
            continue
        if flower_perm[arnold_idx] != 'lilies':
            continue

        for height_perm in itertools.permutations(heights):
            if height_perm[arnold_idx] != 'tall':
                continue

            for mother_perm in itertools.permutations(mothers):
                valid_mother_flower = True
                for i in range(4):
                    if mother_perm[i] == 'Janelle' and flower_perm[i] != 'carnations':
                        valid_mother_flower = False
                        break
                if not valid_mother_flower:
                    continue

                if mother_perm[alice_idx] != 'Aniya':
                    continue

                for occupation_perm in itertools.permutations(occupations):
                    if occupation_perm[0] != 'teacher':
                        continue

                    if occupation_perm[peter_idx] != 'doctor':
                        continue

                    for sport_perm in itertools.permutations(sports):
                        if sport_perm[eric_idx] != 'swimming':
                            continue

                        valid_soccer_short = True
                        for i in range(4):
                            if sport_perm[i] == 'soccer' and height_perm[i] != 'short':
                                valid_soccer_short = False
                                break
                        if not valid_soccer_short:
                            continue

                        valid_basketball_avg = True
                        for i in range(4):
                            if sport_perm[i] == 'basketball' and height_perm[i] != 'average':
                                valid_basketball_avg = False
                                break
                        if not valid_basketball_avg:
                            continue

                        if arnold_idx == 2:
                            continue

                        daffodils_idx = flower_perm.index('daffodils')
                        engineer_idx = occupation_perm.index('engineer')
                        if daffodils_idx <= engineer_idx:
                            continue

                        average_height_idx = height_perm.index('average')
                        holly_idx = mother_perm.index('Holly')
                        if holly_idx <= average_height_idx:
                            continue

                        solution_data = []
                        for i in range(4):
                            house_num = i + 1
                            solution_data.append([
                                str(house_num),
                                name_perm[i],
                                flower_perm[i],
                                height_perm[i],
                                mother_perm[i],
                                occupation_perm[i],
                                sport_perm[i]
                            ])

                        json_output = {
                            "solution": {
                                "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
                                "rows": solution_data
                            }
                        }

                        print(json.dumps(json_output))
                        solution_found = True
                        break
                    if solution_found:
                        break
                if solution_found:
                    break
            if solution_found:
                break
        if solution_found:
            break
    if solution_found:
        break