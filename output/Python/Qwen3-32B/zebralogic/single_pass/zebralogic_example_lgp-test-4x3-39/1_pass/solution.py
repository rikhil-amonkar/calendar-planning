import itertools
import json

def solve_puzzle():
    names = ['Eric', 'Alice', 'Peter', 'Arnold']
    hair_colors = ['blonde', 'black', 'red', 'brown']
    sports = ['swimming', 'soccer', 'basketball', 'tennis']

    for n_perm in itertools.permutations(names):
        for h_perm in itertools.permutations(hair_colors):
            # Check clue 2: Eric has blonde hair
            if h_perm[n_perm.index('Eric')] != 'blonde':
                continue
            for s_perm in itertools.permutations(sports):
                # Check clue 1: soccer not in house 2 (index 1)
                if s_perm[1] == 'soccer':
                    continue
                # Check clue 3: blonde is right of basketball
                blonde_index = h_perm.index('blonde')
                basketball_index = s_perm.index('basketball')
                if not (blonde_index > basketball_index):
                    continue
                # Check clue 4: black hair loves tennis
                black_index = h_perm.index('black')
                if s_perm[black_index] != 'tennis':
                    continue
                # Check clue 5: Arnold left of red hair
                arnold_index = n_perm.index('Arnold')
                red_index = h_perm.index('red')
                if not (arnold_index < red_index):
                    continue
                # Check clue 6: Alice loves swimming
                alice_index = n_perm.index('Alice')
                if s_perm[alice_index] != 'swimming':
                    continue
                # Check clue 7: red directly left of black
                red_index_h = h_perm.index('red')
                if red_index_h + 1 >= len(h_perm) or h_perm[red_index_h + 1] != 'black':
                    continue

                # If all clues passed, build the solution
                rows = []
                for i in range(4):
                    house = str(i + 1)
                    name = n_perm[i]
                    hair = h_perm[i]
                    sport = s_perm[i]
                    rows.append([house, name, hair, sport])
                solution = {
                    "solution": {
                        "header": ["House", "Name", "HairColor", "FavoriteSport"],
                        "rows": rows
                    }
                }
                print(json.dumps(solution))
                return

solve_puzzle()