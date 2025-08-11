import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3']
    names = ['Eric', 'Peter', 'Arnold']
    cigars = ['blue master', 'prince', 'pall mall']
    hobbies = ['photography', 'gardening', 'cooking']
    educations = ['high school', 'associate', 'bachelor']
    drinks = ['tea', 'milk', 'water']

    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for cigar_perm in permutations(cigars):
            for hobby_perm in permutations(hobbies):
                for edu_perm in permutations(educations):
                    for drink_perm in permutations(drinks):
                        # Create a solution candidate
                        candidate = []
                        for i in range(3):
                            candidate.append({
                                'House': str(i+1),
                                'Name': name_perm[i],
                                'cigar': cigar_perm[i],
                                'hobby': hobby_perm[i],
                                'education': edu_perm[i],
                                'drink': drink_perm[i]
                            })

                        # Check all constraints
                        valid = True

                        # Constraint 1: Pall Mall is Peter
                        for house in candidate:
                            if house['cigar'] == 'pall mall' and house['Name'] != 'Peter':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Constraint 2: milk is directly left of high school
                        milk_left_of_hs = False
                        for i in range(2):
                            if candidate[i]['drink'] == 'milk' and candidate[i+1]['education'] == 'high school':
                                milk_left_of_hs = True
                                break
                        if not milk_left_of_hs:
                            valid = False
                            continue

                        # Constraint 3: Eric is the tea drinker
                        for house in candidate:
                            if house['Name'] == 'Eric' and house['drink'] != 'tea':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Constraint 4: Arnold and Prince smoker are next to each other
                        arnold_and_prince_adjacent = False
                        for i in range(3):
                            if candidate[i]['Name'] == 'Arnold':
                                if (i > 0 and candidate[i-1]['cigar'] == 'prince') or \
                                   (i < 2 and candidate[i+1]['cigar'] == 'prince'):
                                    arnold_and_prince_adjacent = True
                                    break
                        if not arnold_and_prince_adjacent:
                            valid = False
                            continue

                        # Constraint 5: gardening is left of Prince smoker
                        prince_pos = -1
                        gardening_pos = -1
                        for i in range(3):
                            if candidate[i]['cigar'] == 'prince':
                                prince_pos = i
                            if candidate[i]['hobby'] == 'gardening':
                                gardening_pos = i
                        if gardening_pos >= prince_pos or prince_pos == -1 or gardening_pos == -1:
                            valid = False
                            continue

                        # Constraint 6: milk drinker has associate's degree
                        for house in candidate:
                            if house['drink'] == 'milk' and house['education'] != 'associate':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Constraint 7: bachelor is directly left of photography
                        bachelor_left_of_photo = False
                        for i in range(2):
                            if candidate[i]['education'] == 'bachelor' and candidate[i+1]['hobby'] == 'photography':
                                bachelor_left_of_photo = True
                                break
                        if not bachelor_left_of_photo:
                            valid = False
                            continue

                        # If all constraints are satisfied, return the solution
                        if valid:
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "cigar", "hobby", "education", "drink"],
                                    "rows": [
                                        [candidate[0]['House'], candidate[0]['Name'], candidate[0]['cigar'], candidate[0]['hobby'], candidate[0]['education'], candidate[0]['drink']],
                                        [candidate[1]['House'], candidate[1]['Name'], candidate[1]['cigar'], candidate[1]['hobby'], candidate[1]['education'], candidate[1]['drink']],
                                        [candidate[2]['House'], candidate[2]['Name'], candidate[2]['cigar'], candidate[2]['hobby'], candidate[2]['education'], candidate[2]['drink']]
                                    ]
                                }
                            }
                            return json.dumps(solution, indent=2)

    return json.dumps({"error": "No solution found"}, indent=2)

print(solve_puzzle())