import itertools
import json

names = ['Eric', 'Alice', 'Peter', 'Arnold']
hair_colors = ['blonde', 'black', 'red', 'brown']
sports = ['swimming', 'soccer', 'basketball', 'tennis']

for name_perm in itertools.permutations(names):
    for hair_perm in itertools.permutations(hair_colors):
        for sport_perm in itertools.permutations(sports):
            # Clue 1: Soccer is not in the second house
            if sport_perm[1] == 'soccer':
                continue
            # Clue 2: Eric has blonde hair
            if hair_perm[name_perm.index('Eric')] != 'blonde':
                continue
            # Clue 3: Blonde is to the right of basketball
            blonde_idx = hair_perm.index('blonde')
            basketball_idx = sport_perm.index('basketball')
            if not (blonde_idx > basketball_idx):
                continue
            # Clue 4: Black hair loves tennis
            black_idx = hair_perm.index('black')
            if sport_perm[black_idx] != 'tennis':
                continue
            # Clue 5: Arnold is left of red hair
            arnold_idx = name_perm.index('Arnold')
            red_idx = hair_perm.index('red')
            if not (arnold_idx < red_idx):
                continue
            # Clue 6: Alice loves swimming
            alice_idx = name_perm.index('Alice')
            if sport_perm[alice_idx] != 'swimming':
                continue
            # Clue 7: Red is directly left of black
            red_idx_clue7 = hair_perm.index('red')
            black_idx_clue7 = hair_perm.index('black')
            if black_idx_clue7 != red_idx_clue7 + 1:
                continue
            # Construct solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "HairColor", "FavoriteSport"],
                    "rows": []
                }
            }
            for i in range(4):
                house_num = str(i + 1)
                solution['solution']['rows'].append([
                    house_num, name_perm[i], hair_perm[i], sport_perm[i]
                ])
            print(json.dumps(solution))
            exit()