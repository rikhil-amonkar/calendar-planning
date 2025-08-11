import json
from itertools import permutations

def solve_puzzle():
    # Define all possible attributes
    names = ['Arnold', 'Eric']
    educations = ['associate', 'high school']
    heights = ['short', 'very short']
    lunches = ['grilled cheese', 'pizza']
    drinks = ['tea', 'water']
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for edu_perm in permutations(educations):
            for height_perm in permutations(heights):
                for lunch_perm in permutations(lunches):
                    for drink_perm in permutations(drinks):
                        # Create a solution candidate
                        solution = {
                            1: {
                                'Name': name_perm[0],
                                'education': edu_perm[0],
                                'height': height_perm[0],
                                'lunch': lunch_perm[0],
                                'drink': drink_perm[0]
                            },
                            2: {
                                'Name': name_perm[1],
                                'education': edu_perm[1],
                                'height': height_perm[1],
                                'lunch': lunch_perm[1],
                                'drink': drink_perm[1]
                            }
                        }
                        
                        # Check all constraints
                        # Clue 5: Arnold is the pizza lover
                        pizza_lover = None
                        for house in [1, 2]:
                            if solution[house]['Name'] == 'Arnold':
                                if solution[house]['lunch'] != 'pizza':
                                    break
                        else:
                            # Clue 1: very short is pizza lover
                            for house in [1, 2]:
                                if solution[house]['height'] == 'very short':
                                    if solution[house]['lunch'] != 'pizza':
                                        break
                            else:
                                # Clue 2: grilled cheese is in house 2
                                if solution[2]['lunch'] == 'grilled cheese':
                                    # Clue 3: high school is pizza lover
                                    for house in [1, 2]:
                                        if solution[house]['education'] == 'high school':
                                            if solution[house]['lunch'] != 'pizza':
                                                break
                                    else:
                                        # Clue 4: tea drinker loves grilled cheese
                                        for house in [1, 2]:
                                            if solution[house]['lunch'] == 'grilled cheese':
                                                if solution[house]['drink'] != 'tea':
                                                    break
                                        else:
                                            # All constraints satisfied
                                            # Prepare the output
                                            output = {
                                                "solution": {
                                                    "header": ["House", "Name", "education", "height", "lunch", "drink"],
                                                    "rows": [
                                                        ["1", solution[1]['Name'], solution[1]['education'], solution[1]['height'], solution[1]['lunch'], solution[1]['drink']],
                                                        ["2", solution[2]['Name'], solution[2]['education'], solution[2]['height'], solution[2]['lunch'], solution[2]['drink']]
                                                }
                                            }
                                            return json.dumps(output, indent=2)

# Solve and print the puzzle
print(solve_puzzle())