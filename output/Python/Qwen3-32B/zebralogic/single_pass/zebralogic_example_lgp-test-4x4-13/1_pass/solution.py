import itertools
import json
import sys

names = ['Alice', 'Peter', 'Arnold', 'Eric']
cigars = ['prince', 'dunhill', 'blue master', 'pall mall']
sports = ['swimming', 'basketball', 'soccer', 'tennis']
drinks = ['coffee', 'water', 'milk', 'tea']

for names_perm in itertools.permutations(names):
    if names_perm[3] != 'Peter':
        continue

    for cigars_perm in itertools.permutations(cigars):
        if cigars_perm[3] != 'pall mall':
            continue

        for sports_perm in itertools.permutations(sports):
            if sports_perm[2] != 'basketball':
                continue

            for drinks_perm in itertools.permutations(drinks):
                if drinks_perm[0] != 'water':
                    continue

                arnold_index = names_perm.index('Arnold')

                if drinks_perm[arnold_index] != 'coffee':
                    continue

                if cigars_perm[arnold_index] != 'blue master':
                    continue

                if names_perm[2] != 'Eric':
                    continue

                if drinks_perm[2] != 'tea':
                    continue

                tennis_index = None
                for i in range(4):
                    if sports_perm[i] == 'tennis':
                        tennis_index = i
                        break
                if tennis_index is None or cigars_perm[tennis_index] != 'blue master':
                    continue

                prince_index = None
                for i in range(4):
                    if cigars_perm[i] == 'prince':
                        prince_index = i
                        break
                if prince_index is None or sports_perm[prince_index] != 'soccer':
                    continue

                solution_rows = []
                for i in range(4):
                    house_num = str(i + 1)
                    name = names_perm[i]
                    cigar = cigars_perm[i]
                    sport = sports_perm[i]
                    drink = drinks_perm[i]
                    solution_rows.append([house_num, name, cigar, sport, drink])

                output = {
                    "solution": {
                        "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
                        "rows": solution_rows
                    }
                }

                print(json.dumps(output))
                sys.exit()