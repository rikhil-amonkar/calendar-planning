import itertools
import json

names = ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob']
mothers = ['Kailyn', 'Janelle', 'Aniya', 'Penny', 'Holly']
heights = ['average', 'very short', 'short', 'very tall', 'tall']

for name_perm in itertools.permutations(names):
    for mother_perm in itertools.permutations(mothers):
        # Check Bob's mother is Janelle
        bob_idx = name_perm.index('Bob')
        if mother_perm[bob_idx] != 'Janelle':
            continue
        # Check Alice's mother is Aniya
        alice_idx = name_perm.index('Alice')
        if mother_perm[alice_idx] != 'Aniya':
            continue
        # Check Eric's mother is Kailyn
        eric_idx = name_perm.index('Eric')
        if mother_perm[eric_idx] != 'Kailyn':
            continue
        # Now process heights
        for height_perm in itertools.permutations(heights):
            # Check house 5 is very short
            if height_perm[4] != 'very short':
                continue
            # Check Arnold's height is very tall
            arnold_idx = name_perm.index('Arnold')
            if height_perm[arnold_idx] != 'very tall':
                continue
            # Check short is directly left of Arnold
            if arnold_idx == 0:
                continue
            if height_perm[arnold_idx - 1] != 'short':
                continue
            # Check Bob is directly left of average
            bob_idx = name_perm.index('Bob')
            if bob_idx >= 4:
                continue
            if height_perm[bob_idx + 1] != 'average':
                continue
            # Check average is left of Penny's mother
            avg_height_pos = height_perm.index('average')
            penny_mother_pos = mother_perm.index('Penny')
            if avg_height_pos >= penny_mother_pos:
                continue
            # Check Holly's mother is left of Arnold
            holly_mother_pos = mother_perm.index('Holly')
            if holly_mother_pos >= arnold_idx:
                continue
            # Check Peter not in house 2 (position 1)
            if name_perm[1] == 'Peter':
                continue
            # Check Eric not in house 5 (position 4)
            if name_perm[4] == 'Eric':
                continue
            # All constraints met
            rows = []
            for i in range(5):
                house_num = str(i + 1)
                name = name_perm[i]
                mother = mother_perm[i]
                height = height_perm[i]
                rows.append([house_num, name, mother, height])
            solution = {
                "solution": {
                    "header": ["House", "Name", "Mother", "Height"],
                    "rows": rows
                }
            }
            print(json.dumps(solution))
            exit()