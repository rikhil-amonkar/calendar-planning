import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ['Eric', 'Alice', 'Peter', 'Bob', 'Arnold']
    children = ['Timothy', 'Meredith', 'Samantha', 'Fred', 'Bella']
    houses = [1, 2, 3, 4, 5]

    # Generate all possible permutations for names and children
    for name_perm in itertools.permutations(names):
        for child_perm in itertools.permutations(children):
            # Unpack the permutations for easier access
            eric, alice, peter, bob, arnold = name_perm
            timothy, meredith, samantha, fred, bella = child_perm

            # Apply the constraints
            if (bob < name_perm.index(samantha) and
                name_perm.index(timothy) < name_perm.index(samantha) and
                child_perm.index(fred) == 1 and
                abs(name_perm.index(alice) - name_perm.index(samantha)) == 2 and
                eric != 2 and
                bob != 2 and
                child_perm.index(bella) == child_perm.index(fred) + 1 and
                name_perm.index(peter) > name_perm.index(samantha)):
                
                # Construct the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Children"],
                        "rows": [
                            [str(houses[0]), name_perm[0], child_perm[0]],
                            [str(houses[1]), name_perm[1], child_perm[1]],
                            [str(houses[2]), name_perm[2], child_perm[2]],
                            [str(houses[3]), name_perm[3], child_perm[3]],
                            [str(houses[4]), name_perm[4], child_perm[4]]
                        ]
                    }
                }

                # Output the solution as JSON
                print(json.dumps(solution, indent=2))
                return

# Run the solver
solve_puzzle()