import itertools
import json

def main():
    # There are 6 houses, indexed 0 to 5 corresponding to houses 1 to 6.
    # Fixed person placements based on clues:
    #   Peter is in the first house -> index 0
    #   Bob is in the third house -> index 2
    #   Carol must be next to Eric and since Eric is in the sixth house -> Carol is in the fifth house -> index 4
    #   Eric is in the sixth house -> index 5
    persons_fixed = {0: "Peter", 2: "Bob", 4: "Carol", 5: "Eric"}
    # The remaining persons for houses at index 1 and 3 are: Arnold and Alice.
    remaining_persons = ["Arnold", "Alice"]
    
    # Fixed cigar placements based on clues:
    #   The Pall Mall smoker is in the third house -> index 2
    #   The Blue Master smoker is in the fifth house -> index 4
    cigars_fixed = {2: "pall mall", 4: "blue master"}
    # The remaining cigars for houses at indices 0, 1, 3, and 5 are:
    remaining_cigars = ["blends", "yellow monster", "dunhill", "prince"]
    
    solution = None
    
    # Iterate over possible assignments for the free person positions (indices 1 and 3)
    for perm_persons in itertools.permutations(remaining_persons):
        persons = [None] * 6
        # Assign the fixed persons.
        for idx, name in persons_fixed.items():
            persons[idx] = name
        # Fill in the remaining positions.
        free_indices_persons = [1, 3]
        for idx, name in zip(free_indices_persons, perm_persons):
            persons[idx] = name
        
        # Iterate over possible assignments for the free cigar positions (indices 0, 1, 3, 5)
        for perm_cigars in itertools.permutations(remaining_cigars):
            cigars = [None] * 6
            # Assign the fixed cigars.
            for idx, cigar in cigars_fixed.items():
                cigars[idx] = cigar
            free_indices_cigars = [0, 1, 3, 5]
            for idx, cigar in zip(free_indices_cigars, perm_cigars):
                cigars[idx] = cigar
            
            # Constraint 1: Arnold is somewhere to the left of the person who smokes blends.
            pos_arnold = persons.index("Arnold")
            pos_blends = cigars.index("blends")
            if pos_arnold >= pos_blends:
                continue
            
            # Constraint 3: Arnold is somewhere to the left of the Prince smoker.
            pos_prince = cigars.index("prince")
            if pos_arnold >= pos_prince:
                continue
            
            # Constraint 4: There is one house between the person who smokes Yellow Monster and the person who smokes blends.
            pos_yellow = cigars.index("yellow monster")
            if abs(pos_yellow - pos_blends) != 2:
                continue
            
            # All constraints satisfied; we've found a valid solution.
            solution = (persons, cigars)
            break
        if solution is not None:
            break

    if solution is None:
        result = {"solution": "No solution found"}
    else:
        persons, cigars = solution
        # Build the final JSON output structure.
        output = {
            "solution": {
                "header": ["House", "Name", "Cigar"],
                "rows": []
            }
        }
        for i in range(6):
            house_number = str(i + 1)
            output["solution"]["rows"].append([house_number, persons[i], cigars[i]])
        result = output

    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()