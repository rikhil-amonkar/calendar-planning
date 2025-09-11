import itertools
import json

names = ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob']
mothers = ['Kailyn', 'Janelle', 'Aniya', 'Penny', 'Holly']
heights = ['average', 'very short', 'short', 'very tall', 'tall']

for name_perm in itertools.permutations(names):
    # Check clue 4: Peter is not in the second house
    if name_perm[1] == 'Peter':
        continue
    # Check clue 8: Eric is not in the fifth house
    if name_perm[4] == 'Eric':
        continue
    for mother_perm in itertools.permutations(mothers):
        for height_perm in itertools.permutations(heights):
            # Check clue 11: The person who is very short is in the fifth house
            if height_perm[4] != 'very short':
                continue
            # Check clue 1: Alice's mother is Aniya
            alice_idx = name_perm.index('Alice')
            if mother_perm[alice_idx] != 'Aniya':
                continue
            # Check clue 3: Bob's mother is Janelle
            bob_idx = name_perm.index('Bob')
            if mother_perm[bob_idx] != 'Janelle':
                continue
            # Check clue 10: Eric's mother is Kailyn
            eric_idx = name_perm.index('Eric')
            if mother_perm[eric_idx] != 'Kailyn':
                continue
            # Check clue 6: Arnold's height is very tall
            arnold_idx = name_perm.index('Arnold')
            if height_perm[arnold_idx] != 'very tall':
                continue
            # Check clue 5: Short is directly left of Arnold
            short_idx = height_perm.index('short')
            if short_idx == 4 or name_perm[short_idx + 1] != 'Arnold':
                continue
            # Check clue 7: Bob is directly left of average height
            if bob_idx == 4 or height_perm[bob_idx + 1] != 'average':
                continue
            # Check clue 2: Average height is left of Penny's mother
            average_idx = height_perm.index('average')
            penny_idx = mother_perm.index('Penny')
            if average_idx >= penny_idx:
                continue
            # Check clue 9: Very tall is right of Holly's mother
            very_tall_idx = arnold_idx
            holly_idx = mother_perm.index('Holly')
            if very_tall_idx <= holly_idx:
                continue
            # All constraints satisfied, build the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "Mother", "Height"],
                    "rows": []
                }
            }
            for i in range(5):
                house_num = str(i + 1)
                name = name_perm[i]
                mother = mother_perm[i]
                height = height_perm[i]
                solution["solution"]["rows"].append([house_num, name, mother, height])
            print(json.dumps(solution))
            exit()

# If no solution is found (should not happen)
print(json.dumps({"solution": {"header": [], "rows": []}}))