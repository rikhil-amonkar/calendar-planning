import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options for each category
    names = ['Peter', 'Alice', 'Eric', 'Arnold']
    mothers = ['Janelle', 'Holly', 'Aniya', 'Kailyn']
    smoothies = ['watermelon', 'dragonfruit', 'desert', 'cherry']
    heights = ['tall', 'average', 'short', 'very short']
    educations = ['high school', 'associate', 'master', 'bachelor']
    
    # Generate all possible permutations for each house
    for name_perm in permutations(names):
        for mother_perm in permutations(mothers):
            for smoothie_perm in permutations(smoothies):
                for height_perm in permutations(heights):
                    for education_perm in permutations(educations):
                        # Create a list of houses with all attributes
                        houses = [
                            {
                                'House': '1',
                                'Name': name_perm[0],
                                'Mother': mother_perm[0],
                                'Smoothie': smoothie_perm[0],
                                'Height': height_perm[0],
                                'Education': education_perm[0]
                            },
                            {
                                'House': '2',
                                'Name': name_perm[1],
                                'Mother': mother_perm[1],
                                'Smoothie': smoothie_perm[1],
                                'Height': height_perm[1],
                                'Education': education_perm[1]
                            },
                            {
                                'House': '3',
                                'Name': name_perm[2],
                                'Mother': mother_perm[2],
                                'Smoothie': smoothie_perm[2],
                                'Height': height_perm[2],
                                'Education': education_perm[2]
                            },
                            {
                                'House': '4',
                                'Name': name_perm[3],
                                'Mother': mother_perm[3],
                                'Smoothie': smoothie_perm[3],
                                'Height': height_perm[3],
                                'Education': education_perm[3]
                            }
                        ]
                        
                        # Check all constraints
                        valid = True
                        
                        # Clue 1: Janelle is in the third house
                        if houses[2]['Mother'] != 'Janelle':
                            valid = False
                            continue
                        
                        # Clue 2: Desert smoothie lover has master's degree
                        for house in houses:
                            if house['Smoothie'] == 'desert' and house['Education'] != 'master':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 3: Desert smoothie lover is not in the first house
                        if houses[0]['Smoothie'] == 'desert':
                            valid = False
                            continue
                        
                        # Clue 4: very short is left of high school
                        very_short_pos = None
                        high_school_pos = None
                        for i, house in enumerate(houses):
                            if house['Height'] == 'very short':
                                very_short_pos = i
                            if house['Education'] == 'high school':
                                high_school_pos = i
                        if very_short_pos is None or high_school_pos is None or very_short_pos >= high_school_pos:
                            valid = False
                            continue
                        
                        # Clue 5: Eric and cherry smoothie are next to each other
                        eric_pos = None
                        cherry_pos = None
                        for i, house in enumerate(houses):
                            if house['Name'] == 'Eric':
                                eric_pos = i
                            if house['Smoothie'] == 'cherry':
                                cherry_pos = i
                        if eric_pos is None or cherry_pos is None or abs(eric_pos - cherry_pos) != 1:
                            valid = False
                            continue
                        
                        # Clue 6: high school not in third house
                        if houses[2]['Education'] == 'high school':
                            valid = False
                            continue
                        
                        # Clue 7: Kailyn's mother has associate's degree
                        for house in houses:
                            if house['Mother'] == 'Kailyn' and house['Education'] != 'associate':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 8: cherry smoothie lover's mother is Aniya
                        for house in houses:
                            if house['Smoothie'] == 'cherry' and house['Mother'] != 'Aniya':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 9: tall person's mother is Janelle
                        for house in houses:
                            if house['Height'] == 'tall' and house['Mother'] != 'Janelle':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 10: Arnold is right of average height
                        average_pos = None
                        arnold_pos = None
                        for i, house in enumerate(houses):
                            if house['Height'] == 'average':
                                average_pos = i
                            if house['Name'] == 'Arnold':
                                arnold_pos = i
                        if average_pos is None or arnold_pos is None or arnold_pos <= average_pos:
                            valid = False
                            continue
                        
                        # Clue 11: dragonfruit lover is directly left of short person
                        dragon_pos = None
                        short_pos = None
                        for i, house in enumerate(houses):
                            if house['Smoothie'] == 'dragonfruit':
                                dragon_pos = i
                            if house['Height'] == 'short':
                                short_pos = i
                        if dragon_pos is None or short_pos is None or (dragon_pos + 1) != short_pos:
                            valid = False
                            continue
                        
                        # Clue 12: tall person is Alice
                        for house in houses:
                            if house['Height'] == 'tall' and house['Name'] != 'Alice':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # If all constraints are satisfied, return the solution
                        if valid:
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"],
                                    "rows": [
                                        [house['House'], house['Name'], house['Mother'], house['Smoothie'], house['Height'], house['Education']]
                                        for house in houses
                                    ]
                                }
                            }
                            return json.dumps(solution, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())