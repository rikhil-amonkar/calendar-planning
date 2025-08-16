import itertools
import json

def solve_puzzle():
    # Define the possible values
    names = ["Arnold", "Eric", "Peter", "Alice"]
    occupations = ["doctor", "engineer", "artist", "teacher"]
    
    # Generate all possible permutations for names and occupations
    permutations = list(itertools.permutations(names))
    occupation_permutations = list(itertools.permutations(occupations))
    
    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(name_perm, occupation_perm):
        # Unpack the permutations
        house1, house2, house3, house4 = name_perm
        occ1, occ2, occ3, occ4 = occupation_perm
        
        # Check clue 2 and 5
        if house3 != "Peter" or occ3 != "teacher" or house4 != "Alice" or occ4 != "artist":
            return False
        
        # Check clue 1
        if abs(name_perm.index("Eric") - name_perm.index("Peter")) != 3:
            return False
        
        # Check clue 3
        if house1 == "Peter":
            return False
        
        # Check clue 4
        if abs(name_perm.index("Alice") - occupation_perm.index("doctor")) != 2:
            return False
        
        return True
    
    # Find the valid solution
    for name_perm in permutations:
        for occupation_perm in occupation_permutations:
            if is_valid_solution(name_perm, occupation_perm):
                # Prepare the solution in the required format
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Occupation"],
                        "rows": [
                            ["1", name_perm[0], occupation_perm[0]],
                            ["2", name_perm[1], occupation_perm[1]],
                            ["3", name_perm[2], occupation_perm[2]],
                            ["4", name_perm[3], occupation_perm[3]]
                        ]
                    }
                }
                return json.dumps(solution)

# Output the solution
print(solve_puzzle())