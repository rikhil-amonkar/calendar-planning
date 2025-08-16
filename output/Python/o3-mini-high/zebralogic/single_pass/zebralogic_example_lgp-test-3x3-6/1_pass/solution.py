#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3]
    names = ["Eric", "Arnold", "Peter"]
    book_genres = ["mystery", "science fiction", "romance"]
    vacations = ["mountain", "beach", "city"]
    
    # Iterate over all possible assignments for names, book_genres, and vacations.
    for name_perm in itertools.permutations(names):
        # Clue 1: Eric is directly left of Arnold.
        valid = False
        for i in range(len(name_perm) - 1):
            if name_perm[i] == "Eric" and name_perm[i+1] == "Arnold":
                valid = True
                break
        if not valid:
            continue
        
        for bg_perm in itertools.permutations(book_genres):
            for vac_perm in itertools.permutations(vacations):
                # Clue 3: Peter is the person who prefers city breaks.
                index_peter = name_perm.index("Peter")
                if vac_perm[index_peter] != "city":
                    continue
                
                # Clue 5: The person who loves science fiction books is the person who loves beach vacations.
                valid_scifi_beach = True
                for i in range(3):
                    if bg_perm[i] == "science fiction" and vac_perm[i] != "beach":
                        valid_scifi_beach = False
                        break
                    if vac_perm[i] == "beach" and bg_perm[i] != "science fiction":
                        valid_scifi_beach = False
                        break
                if not valid_scifi_beach:
                    continue
                
                # Clue 2: Peter is somewhere to the right of the person who loves beach vacations.
                index_beach = vac_perm.index("beach")
                if name_perm.index("Peter") <= index_beach:
                    continue
                
                # Clue 4: The person who loves mystery books is somewhere to the left of the person who loves beach vacations.
                index_mystery = bg_perm.index("mystery")
                if index_mystery >= index_beach:
                    continue
                
                # If all constraints are satisfied, build the solution.
                result = []
                for i in range(3):
                    # House numbers as strings
                    result.append([str(i+1), name_perm[i], bg_perm[i], vac_perm[i]])
                return {"solution": {"header": ["House", "Name", "BookGenre", "Vacation"],
                                     "rows": result}}
    return None

if __name__ == "__main__":
    solution = solve_puzzle()
    if solution is None:
        print(json.dumps({"solution": {}}))
    else:
        print(json.dumps(solution))