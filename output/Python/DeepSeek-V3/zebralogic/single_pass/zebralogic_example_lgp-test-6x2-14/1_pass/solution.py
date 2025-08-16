import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Carol', 'Peter', 'Eric', 'Arnold', 'Alice', 'Bob']
    cigars = ['blends', 'yellow monster', 'pall mall', 'blue master', 'dunhill', 'prince']
    
    # Generate all possible permutations for names and cigars
    for name_perm in permutations(names):
        name_assignment = {house: name for house, name in zip(houses, name_perm)}
        
        # Check constraints related to names
        if name_assignment[1] != 'Peter':
            continue
        if name_assignment[3] != 'Bob':
            continue
        if name_assignment[6] != 'Eric':
            continue
        
        # Carol and Eric are next to each other (Eric is in 6, so Carol must be in 5)
        if name_assignment[5] != 'Carol':
            continue
        
        for cigar_perm in permutations(cigars):
            cigar_assignment = {house: cigar for house, cigar in zip(houses, cigar_perm)}
            
            # Check constraints related to cigars
            if cigar_assignment[5] != 'blue master':
                continue
            if cigar_assignment[3] != 'pall mall':
                continue
            
            # Arnold is left of blends smoker
            blends_house = None
            for house in houses:
                if cigar_assignment[house] == 'blends':
                    blends_house = house
                    break
            if blends_house is None:
                continue
            arnold_house = None
            for house in houses:
                if name_assignment[house] == 'Arnold':
                    arnold_house = house
                    break
            if arnold_house is None or arnold_house >= blends_house:
                continue
            
            # Arnold is left of prince smoker
            prince_house = None
            for house in houses:
                if cigar_assignment[house] == 'prince':
                    prince_house = house
                    break
            if prince_house is None or arnold_house >= prince_house:
                continue
            
            # One house between yellow monster and blends
            yellow_house = None
            for house in houses:
                if cigar_assignment[house] == 'yellow monster':
                    yellow_house = house
                    break
            if yellow_house is None:
                continue
            if abs(yellow_house - blends_house) != 2:
                continue
            
            # All constraints satisfied, prepare solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "Cigar"],
                    "rows": [
                        [str(house), name_assignment[house], cigar_assignment[house]] for house in houses
                    ]
                }
            }
            return json.dumps(solution)
    
    return json.dumps({"solution": {"header": ["House", "Name", "Cigar"], "rows": []}})

print(solve_puzzle())