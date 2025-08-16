#!/usr/bin/env python3
import json
import itertools

def main():
    # Define the houses (indices 0,1,2 correspond to House 1,2,3)
    names = ["Arnold", "Peter", "Eric"]
    heights = ["short", "average", "very short"]
    
    solution_found = None
    
    for name_perm in itertools.permutations(names):
        for height_perm in itertools.permutations(heights):
            # Constraint 2: The person who is short is in the first house.
            if height_perm[0] != "short":
                continue
            
            # Constraint 3: There is one house between the person who is short and the person who is very short.
            index_short = height_perm.index("short")
            index_very_short = height_perm.index("very short")
            if abs(index_short - index_very_short) != 2:
                continue
            
            # Constraint 1: Peter is somewhere to the right of Eric.
            index_peter = name_perm.index("Peter")
            index_eric = name_perm.index("Eric")
            if not (index_peter > index_eric):
                continue
            
            # Constraint 4: Arnold and the person who is very short are next to each other.
            index_arnold = name_perm.index("Arnold")
            if abs(index_arnold - index_very_short) != 1:
                continue
            
            # If all constraints are satisfied, we have found a valid solution.
            solution_found = []
            for i in range(3):
                # House numbers are 1-indexed.
                solution_found.append([str(i+1), name_perm[i], height_perm[i]])
            break
        if solution_found:
            break

    output = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": solution_found if solution_found is not None else []
        }
    }
    print(json.dumps(output, indent=2))
    
if __name__ == '__main__':
    main()