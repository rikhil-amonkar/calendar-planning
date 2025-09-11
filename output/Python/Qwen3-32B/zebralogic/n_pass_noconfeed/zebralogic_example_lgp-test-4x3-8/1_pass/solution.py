import itertools
import json

names = ['Eric', 'Arnold', 'Peter', 'Alice']
hair_colors = ['blonde', 'black', 'brown', 'red']
music_genres = ['pop', 'jazz', 'rock', 'classical']

# Generate valid music permutations: starts with classical and third house is not pop
valid_music_perms = []
for m in itertools.permutations(music_genres):
    if m[0] == 'classical' and m[2] != 'pop':
        valid_music_perms.append(m)

# Generate valid hair permutations: second house is blonde and first house is not brown
valid_hair_perms = []
for h in itertools.permutations(hair_colors):
    if h[1] == 'blonde' and h[0] != 'brown':
        valid_hair_perms.append(h)

for names_perm in itertools.permutations(names):
    for hair_perm in valid_hair_perms:
        for music_perm in valid_music_perms:
            # Check clue 1: Eric has red hair
            eric_index = names_perm.index('Eric')
            if hair_perm[eric_index] != 'red':
                continue

            # Check clue 6: Jazz is at position with red hair and Eric's name
            jazz_index = music_perm.index('jazz')
            if hair_perm[jazz_index] != 'red' or names_perm[jazz_index] != 'Eric':
                continue

            # Check clue 7: Rock is at Arnold's position
            rock_index = music_perm.index('rock')
            if names_perm[rock_index] != 'Arnold':
                continue

            # Check clue 8: Peter is to the right of rock
            peter_index = names_perm.index('Peter')
            if peter_index <= rock_index:
                continue

            # All constraints are satisfied
            solution_rows = []
            for i in range(4):
                house_num = str(i + 1)
                name = names_perm[i]
                hair = hair_perm[i]
                music = music_perm[i]
                solution_rows.append([house_num, name, hair, music])

            solution = {
                "solution": {
                    "header": ["House", "Name", "HairColor", "MusicGenre"],
                    "rows": solution_rows
                }
            }

            print(json.dumps(solution))
            exit()

# If no solution is found (should not happen for a valid puzzle)
print(json.dumps({"solution": {"header": [], "rows": []}}))