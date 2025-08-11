import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3', '4', '5']
    names = ['Arnold', 'Bob', 'Alice', 'Eric', 'Peter']
    heights = ['very tall', 'average', 'tall', 'very short', 'short']
    lunches = ['stew', 'grilled cheese', 'spaghetti', 'pizza', 'stir fry']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for height_perm in permutations(heights):
            for lunch_perm in permutations(lunches):
                # Assign each permutation to houses 1-5
                assignment = []
                for i in range(5):
                    assignment.append({
                        'House': houses[i],
                        'Name': name_perm[i],
                        'Height': height_perm[i],
                        'Lunch': lunch_perm[i]
                    })
                
                # Check all constraints
                valid = True
                
                # Constraint 1: Alice is short
                alice_house = None
                for house in assignment:
                    if house['Name'] == 'Alice':
                        if house['Height'] != 'short':
                            valid = False
                        alice_house = house
                if alice_house is None:
                    valid = False
                
                # Constraint 2: Tall is in house 3
                if assignment[2]['Height'] != 'tall':
                    valid = False
                
                # Constraint 3: Average height is not in house 2
                if assignment[1]['Height'] == 'average':
                    valid = False
                
                # Constraint 4: Average is left of stew
                avg_pos = None
                stew_pos = None
                for i in range(5):
                    if assignment[i]['Height'] == 'average':
                        avg_pos = i
                    if assignment[i]['Lunch'] == 'stew':
                        stew_pos = i
                if avg_pos is None or stew_pos is None or avg_pos >= stew_pos:
                    valid = False
                
                # Constraint 5: Arnold loves stir fry
                arnold_house = None
                for house in assignment:
                    if house['Name'] == 'Arnold':
                        if house['Lunch'] != 'stir fry':
                            valid = False
                        arnold_house = house
                if arnold_house is None:
                    valid = False
                
                # Constraint 6: Pizza lover is tall
                for house in assignment:
                    if house['Lunch'] == 'pizza':
                        if house['Height'] != 'tall':
                            valid = False
                
                # Constraint 7: Eric is tall
                eric_house = None
                for house in assignment:
                    if house['Name'] == 'Eric':
                        if house['Height'] != 'tall':
                            valid = False
                        eric_house = house
                if eric_house is None:
                    valid = False
                
                # Constraint 8: Bob is right of Arnold
                arnold_pos = None
                bob_pos = None
                for i in range(5):
                    if assignment[i]['Name'] == 'Arnold':
                        arnold_pos = i
                    if assignment[i]['Name'] == 'Bob':
                        bob_pos = i
                if arnold_pos is None or bob_pos is None or bob_pos <= arnold_pos:
                    valid = False
                
                # Constraint 9: Grilled cheese is right of Eric
                eric_pos = None
                grilled_pos = None
                for i in range(5):
                    if assignment[i]['Name'] == 'Eric':
                        eric_pos = i
                    if assignment[i]['Lunch'] == 'grilled cheese':
                        grilled_pos = i
                if eric_pos is None or grilled_pos is None or grilled_pos <= eric_pos:
                    valid = False
                
                # Constraint 10: Very short is left of Arnold
                very_short_pos = None
                for i in range(5):
                    if assignment[i]['Height'] == 'very short':
                        very_short_pos = i
                if very_short_pos is None or arnold_pos is None or very_short_pos >= arnold_pos:
                    valid = False
                
                if valid:
                    # Prepare the solution in the required format
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Height", "Lunch"],
                            "rows": []
                        }
                    }
                    for house in assignment:
                        solution["solution"]["rows"].append([
                            house['House'],
                            house['Name'],
                            house['Height'],
                            house['Lunch']
                        ])
                    return solution
    
    return {"solution": {"header": [], "rows": []}}

# Execute and print the solution
solution = solve_puzzle()
print(json.dumps(solution, indent=2))