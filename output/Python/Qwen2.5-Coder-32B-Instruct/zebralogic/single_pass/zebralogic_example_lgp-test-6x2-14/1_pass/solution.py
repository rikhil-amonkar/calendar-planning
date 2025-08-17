import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Carol", "Peter", "Eric", "Arnold", "Alice", "Bob"]
    cigars = ["blends", "yellow monster", "pall mall", "blue master", "dunhill", "prince"]

    # Generate all possible permutations for names and cigars
    for name_perm in itertools.permutations(names):
        for cigar_perm in itertools.permutations(cigars):
            # Unpack permutations for easier access
            name_map = dict(zip(houses, name_perm))
            cigar_map = dict(zip(houses, cigar_perm))

            # Apply constraints
            if (name_map[1] == "Peter" and
                name_map[3] == "Bob" and
                name_map[6] == "Eric" and
                cigar_map[5] == "blue master" and
                cigar_map[3] == "pall mall" and
                abs(name_perm.index("Carol") - name_perm.index("Eric")) == 1 and
                name_perm.index("Arnold") < cigar_perm.index("blends") and
                name_perm.index("Arnold") < cigar_perm.index("prince") and
                abs(cigar_perm.index("yellow monster") - cigar_perm.index("blends")) == 2):
                
                # Construct the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Cigar"],
                        "rows": []
                    }
                }
                
                for house in houses:
                    solution["solution"]["rows"].append([
                        str(house),
                        name_map[house],
                        cigar_map[house]
                    ])
                
                return json.dumps(solution, indent=2)

# Print the solution
print(solve_puzzle())