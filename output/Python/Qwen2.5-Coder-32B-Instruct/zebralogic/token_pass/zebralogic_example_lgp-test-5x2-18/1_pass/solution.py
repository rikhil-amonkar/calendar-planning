import itertools
import json

def solve_puzzle():
    # Define the sets
    people = ['Eric', 'Alice', 'Peter', 'Bob', 'Arnold']
    children = ['Timothy', 'Meredith', 'Samantha', 'Fred', 'Bella']
    houses = [1, 2, 3, 4, 5]

    # Generate all permutations for people and children
    for people_perm in itertools.permutations(people):
        for children_perm in itertools.permutations(children):
            # Unpack the permutations for easier access
            bob_index = people_perm.index('Bob')
            timothy_mother_index = people_perm.index(next(p for p, c in zip(people_perm, children_perm) if c == 'Timothy'))
            samantha_child_index = children_perm.index('Samantha')
            fred_child_index = children_perm.index('Fred')
            bella_child_index = children_perm.index('Bella')
            alice_index = people_perm.index('Alice')
            eric_index = people_perm.index('Eric')
            peter_index = people_perm.index('Peter')

            # Check the constraints
            if (bob_index < samantha_child_index and  # Clue 1
                timothy_mother_index < samantha_child_index and  # Clue 2
                fred_child_index == 1 and  # Clue 3
                abs(alice_index - samantha_child_index) == 2 and  # Clue 4
                eric_index != 2 and  # Clue 5
                bob_index != 2 and  # Clue 6
                fred_child_index + 1 == bella_child_index and  # Clue 7
                peter_index > samantha_child_index):  # Clue 8

                # If all constraints are satisfied, format the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Children"],
                        "rows": []
                    }
                }

                for house in range(5):
                    solution["solution"]["rows"].append([
                        str(house + 1),
                        people_perm[house],
                        children_perm[house]
                    ])

                return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())