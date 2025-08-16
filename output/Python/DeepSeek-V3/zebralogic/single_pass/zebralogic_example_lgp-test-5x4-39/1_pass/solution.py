import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options for each category
    names = ['Arnold', 'Peter', 'Eric', 'Alice', 'Bob']
    hobbies = ['painting', 'cooking', 'knitting', 'gardening', 'photography']
    heights = ['very tall', 'tall', 'very short', 'average', 'short']
    foods = ['stew', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza']
    
    # Initialize houses
    houses = [1, 2, 3, 4, 5]
    
    # We'll use a brute-force approach with pruning based on constraints
    for name_perm in permutations(names):
        # Constraint 3: Peter is not in the second house
        if name_perm[1] == 'Peter':
            continue
        
        # Constraint 8: Eric is not in the fifth house
        if name_perm[4] == 'Eric':
            continue
        
        # Constraint 14: Alice is to the right of the photography enthusiast (Bob)
        try:
            alice_pos = name_perm.index('Alice')
            bob_pos = name_perm.index('Bob')
            if alice_pos < bob_pos:
                continue
        except ValueError:
            continue
        
        for hobby_perm in permutations(hobbies):
            # Constraint 1: Bob is the photography enthusiast
            if hobby_perm[name_perm.index('Bob')] != 'photography':
                continue
            
            for height_perm in permutations(heights):
                # Constraint 12: very short is in house 5
                if height_perm[4] != 'very short':
                    continue
                
                # Constraint 13: tall is in house 3
                if height_perm[2] != 'tall':
                    continue
                
                # Constraint 9: short is Peter
                peter_pos = name_perm.index('Peter')
                if height_perm[peter_pos] != 'short':
                    continue
                
                # Constraint 5: cooking hobby has average height
                cooking_pos = hobby_perm.index('cooking')
                if height_perm[cooking_pos] != 'average':
                    continue
                
                for food_perm in permutations(foods):
                    # Constraint 2: grilled cheese eater is tall
                    grilled_cheese_pos = food_perm.index('grilled cheese')
                    if height_perm[grilled_cheese_pos] != 'tall':
                        continue
                    
                    # Constraint 4: tall person is directly left of stir fry lover
                    tall_pos = height_perm.index('tall')
                    if tall_pos == 4 or food_perm[tall_pos + 1] != 'stir fry':
                        continue
                    
                    # Constraint 6: Alice is directly left of pizza lover
                    try:
                        alice_pos = name_perm.index('Alice')
                        if alice_pos == 4 or food_perm[alice_pos + 1] != 'pizza':
                            continue
                    except ValueError:
                        continue
                    
                    # Constraint 7: spaghetti eater is not in house 2
                    if food_perm[1] == 'spaghetti':
                        continue
                    
                    # Constraint 10: average height and gardening are next to each other
                    avg_pos = height_perm.index('average')
                    gardening_pos = hobby_perm.index('gardening')
                    if abs(avg_pos - gardening_pos) != 1:
                        continue
                    
                    # Constraint 11: painting is directly left of grilled cheese
                    painting_pos = hobby_perm.index('painting')
                    if painting_pos == 4 or food_perm[painting_pos + 1] != 'grilled cheese':
                        continue
                    
                    # All constraints satisfied, build solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Hobby", "Height", "Food"],
                            "rows": []
                        }
                    }
                    for i in range(5):
                        solution["solution"]["rows"].append([
                            str(i+1),
                            name_perm[i],
                            hobby_perm[i],
                            height_perm[i],
                            food_perm[i]
                        ])
                    return json.dumps(solution)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())