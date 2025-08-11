#!/usr/bin/env python3
import json
from itertools import permutations

def solve():
    houses = [1, 2, 3, 4]
    names = ['Arnold', 'Eric', 'Peter', 'Alice']
    occupations = ['doctor', 'engineer', 'artist', 'teacher']
    solutions = []
    
    # Iterate over all possible assignments for names and occupations to houses
    for name_perm in permutations(names):
        # Clue 3: Peter is not in the first house.
        if name_perm[0] == 'Peter':
            continue
        
        # Clue 1: There are two houses between Eric and Peter.
        index_eric = name_perm.index('Eric')
        index_peter = name_perm.index('Peter')
        if abs(index_eric - index_peter) != 3:
            continue
        
        for occ_perm in permutations(occupations):
            valid = True
            
            # Clue 2: The person who is a teacher is Peter.
            for i in range(4):
                if name_perm[i] == 'Peter' and occ_perm[i] != 'teacher':
                    valid = False
                    break
            
            # Clue 5: The person who is an artist is Alice.
            for i in range(4):
                if name_perm[i] == 'Alice' and occ_perm[i] != 'artist':
                    valid = False
                    break
            
            if not valid:
                continue
            
            # Clue 4: There is one house between the person who is a doctor and Alice.
            try:
                index_doctor = occ_perm.index('doctor')
            except ValueError:
                valid = False
                continue
            index_alice = name_perm.index('Alice')
            if abs(index_doctor - index_alice) != 2:
                valid = False
            
            if not valid:
                continue
            
            # Construct the solution based on valid assignment
            solution = []
            for house_num, name, occ in zip(houses, name_perm, occ_perm):
                solution.append([str(house_num), name, occ])
            solutions.append(solution)
    
    return solutions

def main():
    sol = solve()
    # Assuming a unique solution exists, pick the first one.
    if sol:
        result = {
            "solution": {
                "header": ["House", "Name", "Occupation"],
                "rows": sol[0]
            }
        }
    else:
        result = {"solution": {}}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()