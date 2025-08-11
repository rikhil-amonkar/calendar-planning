import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3', '4']
    names = ['Arnold', 'Alice', 'Eric', 'Peter']
    hobbies = ['cooking', 'painting', 'photography', 'gardening']
    months = ['april', 'jan', 'sept', 'feb']
    educations = ['master', 'bachelor', 'associate', 'high school']
    smoothies = ['cherry', 'watermelon', 'desert', 'dragonfruit']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for hobby_perm in permutations(hobbies):
            for month_perm in permutations(months):
                for edu_perm in permutations(educations):
                    for smoothie_perm in permutations(smoothies):
                        # Assign each permutation to houses
                        assignment = []
                        for i in range(4):
                            assignment.append({
                                'House': houses[i],
                                'Name': name_perm[i],
                                'hobby': hobby_perm[i],
                                'birthday month': month_perm[i],
                                'education': edu_perm[i],
                                'smoothie': smoothie_perm[i]
                            })
                        
                        # Check all constraints
                        valid = True
                        
                        # Clue 1: Desert smoothie lover's birthday is jan
                        for house in assignment:
                            if house['smoothie'] == 'desert' and house['birthday month'] != 'jan':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 2: Eric has bachelor's degree
                        for house in assignment:
                            if house['Name'] == 'Eric' and house['education'] != 'bachelor':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 3: jan birthday has bachelor's degree
                        for house in assignment:
                            if house['birthday month'] == 'jan' and house['education'] != 'bachelor':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 4: high school is in house 3
                        if assignment[2]['education'] != 'high school':
                            valid = False
                            continue
                        
                        # Clue 5: Watermelon not in house 3
                        if assignment[2]['smoothie'] == 'watermelon':
                            valid = False
                            continue
                        
                        # Clue 6: Arnold has associate's degree
                        for house in assignment:
                            if house['Name'] == 'Arnold' and house['education'] != 'associate':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 7: master's degree paints
                        for house in assignment:
                            if house['education'] == 'master' and house['hobby'] != 'painting':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 8: one house between dragonfruit and sept birthday
                        dragonfruit_house = None
                        sept_house = None
                        for i, house in enumerate(assignment):
                            if house['smoothie'] == 'dragonfruit':
                                dragonfruit_house = i + 1  # 1-based
                            if house['birthday month'] == 'sept':
                                sept_house = i + 1
                        if dragonfruit_house is None or sept_house is None:
                            valid = False
                            continue
                        if abs(dragonfruit_house - sept_house) != 2:
                            valid = False
                            continue
                        
                        # Clue 9: high school diploma is sept birthday
                        if assignment[2]['birthday month'] != 'sept':
                            valid = False
                            continue
                        
                        # Clue 10: Alice loves cooking
                        for house in assignment:
                            if house['Name'] == 'Alice' and house['hobby'] != 'cooking':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 11: april birthday and gardening are next to each other
                        april_house = None
                        gardening_house = None
                        for i, house in enumerate(assignment):
                            if house['birthday month'] == 'april':
                                april_house = i + 1
                            if house['hobby'] == 'gardening':
                                gardening_house = i + 1
                        if april_house is None or gardening_house is None:
                            valid = False
                            continue
                        if abs(april_house - gardening_house) != 1:
                            valid = False
                            continue
                        
                        # Clue 12: painter's birthday is feb
                        for house in assignment:
                            if house['hobby'] == 'painting' and house['birthday month'] != 'feb':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # If all constraints are satisfied, return the solution
                        if valid:
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "hobby", "birthday month", "education", "smoothie"],
                                    "rows": []
                                }
                            }
                            for house in assignment:
                                solution["solution"]["rows"].append([
                                    house['House'],
                                    house['Name'],
                                    house['hobby'],
                                    house['birthday month'],
                                    house['education'],
                                    house['smoothie']
                                ])
                            return solution
    return None

solution = solve_puzzle()
print(json.dumps(solution, indent=2))