import json
from itertools import permutations

def solve_puzzle():
    # Define the domains
    names = ['Alice', 'Arnold', 'Peter', 'Eric']
    hair_colors = ['black', 'blonde', 'brown', 'red']
    houses = [1, 2, 3, 4]
    
    # Generate all possible assignments
    for name_perm in permutations(names):
        for hair_perm in permutations(hair_colors):
            assignment = list(zip(name_perm, hair_perm))
            
            # Check clue 5: Alice is in the first house
            if assignment[0][0] != 'Alice':
                continue
                
            # Check clue 4: The person who has black hair is not in the first house
            if assignment[0][1] == 'black':
                continue
                
            # Check clue 3: Eric is the person who has brown hair
            eric_house = None
            for i, (name, hair) in enumerate(assignment):
                if name == 'Eric':
                    eric_house = i + 1
                    if hair != 'brown':
                        break
            else:
                if eric_house is None:
                    continue
                    
                # Check clue 1: Eric is directly left of the person who has blonde hair
                if eric_house == 4:  # Eric can't be left of anyone if in last house
                    continue
                if assignment[eric_house][1] != 'blonde':  # Person to Eric's right has blonde hair
                    continue
                    
                # Check clue 2: Alice and Arnold are next to each other
                alice_pos = None
                arnold_pos = None
                for i, (name, _) in enumerate(assignment):
                    if name == 'Alice':
                        alice_pos = i + 1
                    if name == 'Arnold':
                        arnold_pos = i + 1
                
                if alice_pos is None or arnold_pos is None:
                    continue
                    
                if abs(alice_pos - arnold_pos) != 1:
                    continue
                    
                # Found valid solution
                result = []
                for i, (name, hair) in enumerate(assignment):
                    result.append([str(i + 1), name, hair])
                
                return {
                    "solution": {
                        "header": ["House", "Name", "HairColor"],
                        "rows": result
                    }
                }
    
    return {"solution": {"header": ["House", "Name", "HairColor"], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))