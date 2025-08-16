import json
from itertools import permutations

def solve_puzzle():
    # Define possible values
    names = ['Alice', 'Arnold', 'Peter', 'Eric']
    hair_colors = ['black', 'blonde', 'brown', 'red']
    houses = ['1', '2', '3', '4']
    
    # Generate all possible permutations for names and hair colors
    for name_perm in permutations(names):
        # Check clue 5: Alice is in the first house
        if name_perm[0] != 'Alice':
            continue
        
        for hair_perm in permutations(hair_colors):
            # Check clue 4: The person who has black hair is not in the first house
            if hair_perm[0] == 'black':
                continue
            
            # Check clue 3: Eric has brown hair
            eric_index = name_perm.index('Eric')
            if hair_perm[eric_index] != 'brown':
                continue
            
            # Check clue 1: Eric is directly left of the person who has blonde hair
            if eric_index + 1 >= len(houses):
                continue  # Eric is in the last house, can't be directly left
            if hair_perm[eric_index + 1] != 'blonde':
                continue
            
            # Check clue 2: Alice and Arnold are next to each other
            alice_index = name_perm.index('Alice')
            arnold_index = name_perm.index('Arnold')
            if abs(alice_index - arnold_index) != 1:
                continue
            
            # If all clues are satisfied, construct the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "HairColor"],
                    "rows": []
                }
            }
            for i in range(len(houses)):
                solution["solution"]["rows"].append([
                    houses[i],
                    name_perm[i],
                    hair_perm[i]
                ])
            return solution
    
    return {"solution": {"header": ["House", "Name", "HairColor"], "rows": []}}

# Execute and print the solution
print(json.dumps(solve_puzzle(), indent=2))