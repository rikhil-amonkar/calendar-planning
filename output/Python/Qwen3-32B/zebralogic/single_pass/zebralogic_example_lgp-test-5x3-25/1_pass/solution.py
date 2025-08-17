import itertools
import json

def solve_puzzle():
    names = ['Arnold', 'Bob', 'Alice', 'Eric', 'Peter']
    heights = ['very tall', 'average', 'tall', 'very short', 'short']
    foods = ['stew', 'grilled cheese', 'spaghetti', 'pizza', 'stir fry']
    
    valid_name_perms = [p for p in itertools.permutations(names) if p[2] == 'Eric']
    valid_height_perms = [p for p in itertools.permutations(heights) if p[2] == 'tall']
    valid_food_perms = [p for p in itertools.permutations(foods) if p[2] == 'pizza']
    
    for name_perm in valid_name_perms:
        for height_perm in valid_height_perms:
            # Check if Alice's height is 'short'
            alice_pos = name_perm.index('Alice')
            if height_perm[alice_pos] != 'short':
                continue
            for food_perm in valid_food_perms:
                # Check if Arnold's food is 'stir fry'
                arnold_pos = name_perm.index('Arnold')
                if food_perm[arnold_pos] != 'stir fry':
                    continue
                # Check clue 3: average height not in house 2 (index 1)
                avg_height_pos = -1
                for i, h in enumerate(height_perm):
                    if h == 'average':
                        avg_height_pos = i
                        break
                if avg_height_pos == 1:
                    continue
                # Check clue 4: average height is to the left of stew
                stew_pos = food_perm.index('stew')
                if avg_height_pos >= stew_pos:
                    continue
                # Check clue 8: Bob is to the right of Arnold
                bob_pos = name_perm.index('Bob')
                if arnold_pos >= bob_pos:
                    continue
                # Check clue 9: grilled cheese is to the right of Eric (index 2)
                gc_pos = food_perm.index('grilled cheese')
                if gc_pos <= 2:
                    continue
                # Check clue 10: very short is to the left of Arnold
                vs_pos = -1
                for i, h in enumerate(height_perm):
                    if h == 'very short':
                        vs_pos = i
                        break
                if vs_pos >= arnold_pos:
                    continue
                # All constraints passed, build the solution
                rows = []
                for i in range(5):
                    house_num = str(i + 1)
                    name = name_perm[i]
                    height = height_perm[i]
                    food = food_perm[i]
                    rows.append([house_num, name, height, food])
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Height", "Food"],
                        "rows": rows
                    }
                }
                print(json.dumps(solution))
                return

solve_puzzle()