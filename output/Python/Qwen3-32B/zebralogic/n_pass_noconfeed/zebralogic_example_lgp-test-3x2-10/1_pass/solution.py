import itertools
import json

def solve_puzzle():
    names = ['Eric', 'Arnold', 'Peter']
    heights = ['short', 'very short', 'average']
    
    for name_perm in itertools.permutations(names):
        # Check if Eric or Arnold is in the first house
        if name_perm[0] in ['Eric', 'Arnold']:
            continue
        
        for height_perm in itertools.permutations(heights):
            # Check if Eric's height is 'very short'
            eric_index = None
            for i in range(3):
                if name_perm[i] == 'Eric':
                    eric_index = i
                    break
            if height_perm[eric_index] != 'very short':
                continue
            
            # Check if 'very short' is to the left of 'short'
            vs_pos = None
            s_pos = None
            for i in range(3):
                if height_perm[i] == 'very short':
                    vs_pos = i
                if height_perm[i] == 'short':
                    s_pos = i
            if vs_pos >= s_pos:
                continue
            
            # Construct the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "Height"],
                    "rows": []
                }
            }
            for i in range(3):
                house_num = str(i + 1)
                name = name_perm[i]
                height = height_perm[i]
                solution["solution"]["rows"].append([house_num, name, height])
            
            print(json.dumps(solution))
            return

solve_puzzle()