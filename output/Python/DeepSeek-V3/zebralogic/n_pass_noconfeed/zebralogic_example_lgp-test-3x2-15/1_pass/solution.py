import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3]
    names = ['Arnold', 'Peter', 'Eric']
    heights = ['short', 'average', 'very short']
    
    # Generate all possible permutations
    for name_perm in permutations(names):
        for height_perm in permutations(heights):
            assignment = {
                1: {'Name': name_perm[0], 'Height': height_perm[0]},
                2: {'Name': name_perm[1], 'Height': height_perm[1]},
                3: {'Name': name_perm[2], 'Height': height_perm[2]}
            }
            
            # Check all constraints
            # Clue 1: Peter is somewhere to the right of Eric
            peter_house = None
            eric_house = None
            for house in houses:
                if assignment[house]['Name'] == 'Peter':
                    peter_house = house
                if assignment[house]['Name'] == 'Eric':
                    eric_house = house
            if peter_house <= eric_house:
                continue
                
            # Clue 2: The person who is short is in the first house
            if assignment[1]['Height'] != 'short':
                continue
                
            # Clue 3: There is one house between the person who is short and the person who is very short
            short_house = None
            very_short_house = None
            for house in houses:
                if assignment[house]['Height'] == 'short':
                    short_house = house
                if assignment[house]['Height'] == 'very short':
                    very_short_house = house
            if abs(short_house - very_short_house) != 2:
                continue
                
            # Clue 4: Arnold and the person who is very short are next to each other
            arnold_house = None
            for house in houses:
                if assignment[house]['Name'] == 'Arnold':
                    arnold_house = house
            if abs(arnold_house - very_short_house) != 1:
                continue
                
            # If we reach here, all constraints are satisfied
            solution = {
                "solution": {
                    "header": ["House", "Name", "Height"],
                    "rows": [
                        ["1", assignment[1]['Name'], assignment[1]['Height']],
                        ["2", assignment[2]['Name'], assignment[2]['Height']],
                        ["3", assignment[3]['Name'], assignment[3]['Height']]
                    ]
                }
            }
            return solution
    
    return {"solution": {"header": ["House", "Name", "Height"], "rows": []}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))