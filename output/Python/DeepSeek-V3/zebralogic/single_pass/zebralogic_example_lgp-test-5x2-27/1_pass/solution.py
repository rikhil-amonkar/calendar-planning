import itertools
import json

def solve_puzzle():
    # Define all possible values
    houses = [1, 2, 3, 4, 5]
    names = ['Peter', 'Alice', 'Bob', 'Eric', 'Arnold']
    heights = ['very tall', 'average', 'tall', 'very short', 'short']

    # Generate all possible permutations for names and heights
    for name_perm in itertools.permutations(names):
        for height_perm in itertools.permutations(heights):
            solution = {
                1: {'name': None, 'height': None},
                2: {'name': None, 'height': None},
                3: {'name': None, 'height': None},
                4: {'name': None, 'height': None},
                5: {'name': None, 'height': None}
            }

            # Assign names and heights to houses
            for i in range(5):
                solution[i+1]['name'] = name_perm[i]
                solution[i+1]['height'] = height_perm[i]

            # Check all constraints
            valid = True

            # Constraint 1: The person who is short is in the second house.
            if solution[2]['height'] != 'short':
                valid = False
                continue

            # Constraint 2: Peter is directly left of Bob.
            peter_pos = None
            bob_pos = None
            for house in solution:
                if solution[house]['name'] == 'Peter':
                    peter_pos = house
                if solution[house]['name'] == 'Bob':
                    bob_pos = house
            if peter_pos is None or bob_pos is None or bob_pos != peter_pos + 1:
                valid = False
                continue

            # Constraint 3: Eric is somewhere to the left of Peter.
            eric_pos = None
            for house in solution:
                if solution[house]['name'] == 'Eric':
                    eric_pos = house
            if eric_pos is None or eric_pos >= peter_pos:
                valid = False
                continue

            # Constraint 4: The person who is very tall is directly left of Peter.
            very_tall_pos = None
            for house in solution:
                if solution[house]['height'] == 'very tall':
                    very_tall_pos = house
            if very_tall_pos is None or very_tall_pos != peter_pos - 1:
                valid = False
                continue

            # Constraint 5: Alice is directly left of the person who has an average height.
            alice_pos = None
            average_pos = None
            for house in solution:
                if solution[house]['name'] == 'Alice':
                    alice_pos = house
                if solution[house]['height'] == 'average':
                    average_pos = house
            if alice_pos is None or average_pos is None or average_pos != alice_pos + 1:
                valid = False
                continue

            # Constraint 6: The person who is short and the person who is very short are next to each other.
            short_pos = 2  # from constraint 1
            very_short_pos = None
            for house in solution:
                if solution[house]['height'] == 'very short':
                    very_short_pos = house
            if very_short_pos is None or abs(short_pos - very_short_pos) != 1:
                valid = False
                continue

            # Constraint 7: The person who has an average height is in the fifth house.
            if solution[5]['height'] != 'average':
                valid = False
                continue

            if valid:
                # Prepare the output
                output = {
                    "solution": {
                        "header": ["House", "Name", "height"],
                        "rows": []
                    }
                }
                for house in sorted(solution.keys()):
                    row = [str(house), solution[house]['name'], solution[house]['height']]
                    output["solution"]["rows"].append(row)
                return json.dumps(output, indent=2)

    return json.dumps({"error": "No solution found"}, indent=2)

print(solve_puzzle())