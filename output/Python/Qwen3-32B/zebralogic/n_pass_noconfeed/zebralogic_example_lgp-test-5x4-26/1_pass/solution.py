import itertools
import json

names = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
heights = ['average', 'short', 'tall', 'very short', 'very tall']
mothers = ['Janelle', 'Kailyn', 'Penny', 'Holly', 'Aniya']
hair_colors = ['blonde', 'black', 'gray', 'red', 'brown']

for names_perm in itertools.permutations(names):
    if names_perm[4] != 'Bob':
        continue
    for mothers_perm in itertools.permutations(mothers):
        if mothers_perm[2] != 'Kailyn':
            continue
        for heights_perm in itertools.permutations(heights):
            avg_idx = heights_perm.index('average')
            short_idx = heights_perm.index('short')
            if abs(short_idx - avg_idx) != 3:
                continue
            if heights_perm[3] != 'short':
                continue
            for hair_perm in itertools.permutations(hair_colors):
                if hair_perm[3] == 'black':
                    continue
                eric_idx = names_perm.index('Eric')
                if hair_perm[eric_idx] != 'black':
                    continue
                gray_idx = hair_perm.index('gray')
                if abs(eric_idx - gray_idx) != 1:
                    continue
                peter_idx = names_perm.index('Peter')
                if hair_perm[peter_idx] != 'red':
                    continue
                arnold_idx = names_perm.index('Arnold')
                if hair_perm[arnold_idx] != 'brown':
                    continue
                janelle_mother_idx = mothers_perm.index('Janelle')
                if arnold_idx >= janelle_mother_idx:
                    continue
                if gray_idx + 1 != janelle_mother_idx:
                    continue
                vs_idx = heights_perm.index('very short')
                if mothers_perm[vs_idx] != 'Penny':
                    continue
                aniya_mother_idx = mothers_perm.index('Aniya')
                if abs(aniya_mother_idx - vs_idx) != 1:
                    continue
                tall_idx = heights_perm.index('tall')
                if mothers_perm[tall_idx] != 'Holly':
                    continue
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Height", "Mother", "HairColor"],
                        "rows": []
                    }
                }
                for i in range(5):
                    house_num = i + 1
                    name = names_perm[i]
                    height = heights_perm[i]
                    mother = mothers_perm[i]
                    hair = hair_perm[i]
                    solution["solution"]["rows"].append([
                        str(house_num), name, height, mother, hair
                    ])
                print(json.dumps(solution))
                exit()