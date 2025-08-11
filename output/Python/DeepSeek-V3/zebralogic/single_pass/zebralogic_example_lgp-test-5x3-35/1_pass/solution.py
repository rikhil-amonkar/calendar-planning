import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob']
    mothers = ['Kailyn', 'Janelle', 'Aniya', 'Penny', 'Holly']
    heights = ['average', 'very short', 'short', 'very tall', 'tall']
    houses = ['1', '2', '3', '4', '5']

    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for mother_perm in permutations(mothers):
            for height_perm in permutations(heights):
                # Create a dictionary to hold the current assignment
                assignment = []
                for i in range(5):
                    assignment.append({
                        'House': str(i+1),
                        'Name': name_perm[i],
                        'Mother': mother_perm[i],
                        'Height': height_perm[i]
                    })

                # Check all constraints
                valid = True

                # Constraint 1: Alice's mother is Aniya
                alice_house = None
                for house in assignment:
                    if house['Name'] == 'Alice':
                        alice_house = house
                        break
                if alice_house and alice_house['Mother'] != 'Aniya':
                    valid = False

                # Constraint 2: average height is left of Penny's mother
                avg_house_pos = None
                penny_house_pos = None
                for i, house in enumerate(assignment):
                    if house['Height'] == 'average':
                        avg_house_pos = i
                    if house['Mother'] == 'Penny':
                        penny_house_pos = i
                if avg_house_pos is not None and penny_house_pos is not None:
                    if avg_house_pos >= penny_house_pos:
                        valid = False
                elif penny_house_pos is not None and avg_house_pos is None:
                    valid = False  # average must exist if Penny exists

                # Constraint 3: Janelle is Bob's mother
                bob_house = None
                for house in assignment:
                    if house['Name'] == 'Bob':
                        bob_house = house
                        break
                if bob_house and bob_house['Mother'] != 'Janelle':
                    valid = False

                # Constraint 4: Peter is not in the second house
                if assignment[1]['Name'] == 'Peter':
                    valid = False

                # Constraint 5: short is directly left of Arnold
                short_pos = None
                arnold_pos = None
                for i, house in enumerate(assignment):
                    if house['Height'] == 'short':
                        short_pos = i
                    if house['Name'] == 'Arnold':
                        arnold_pos = i
                if short_pos is not None and arnold_pos is not None:
                    if arnold_pos != short_pos + 1:
                        valid = False
                elif arnold_pos is not None:  # short must exist if Arnold exists
                    valid = False

                # Constraint 6: very tall is Arnold
                for house in assignment:
                    if house['Name'] == 'Arnold' and house['Height'] != 'very tall':
                        valid = False
                    if house['Height'] == 'very tall' and house['Name'] != 'Arnold':
                        valid = False

                # Constraint 7: Bob is directly left of average height
                bob_pos = None
                avg_pos = None
                for i, house in enumerate(assignment):
                    if house['Name'] == 'Bob':
                        bob_pos = i
                    if house['Height'] == 'average':
                        avg_pos = i
                if bob_pos is not None and avg_pos is not None:
                    if avg_pos != bob_pos + 1:
                        valid = False
                elif bob_pos is not None:  # average must exist if Bob exists
                    valid = False

                # Constraint 8: Eric is not in the fifth house
                if assignment[4]['Name'] == 'Eric':
                    valid = False

                # Constraint 9: very tall is right of Holly's mother
                very_tall_pos = None
                holly_pos = None
                for i, house in enumerate(assignment):
                    if house['Height'] == 'very tall':
                        very_tall_pos = i
                    if house['Mother'] == 'Holly':
                        holly_pos = i
                if very_tall_pos is not None and holly_pos is not None:
                    if very_tall_pos <= holly_pos:
                        valid = False
                elif very_tall_pos is not None:  # holly must exist if very tall exists
                    valid = False

                # Constraint 10: Eric's mother is Kailyn
                eric_house = None
                for house in assignment:
                    if house['Name'] == 'Eric':
                        eric_house = house
                        break
                if eric_house and eric_house['Mother'] != 'Kailyn':
                    valid = False

                # Constraint 11: very short is in the fifth house
                if assignment[4]['Height'] != 'very short':
                    valid = False

                if valid:
                    # Prepare the solution in the required format
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Mother", "Height"],
                            "rows": []
                        }
                    }
                    for house in assignment:
                        solution["solution"]["rows"].append([
                            house['House'],
                            house['Name'],
                            house['Mother'],
                            house['Height']
                        ])
                    return solution

    return {"solution": {"header": [], "rows": []}}

# Solve the puzzle and print the result as JSON
solution = solve_puzzle()
print(json.dumps(solution, indent=2))