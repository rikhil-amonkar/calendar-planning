import itertools
import json

def solve_puzzle():
    # Define all possible categories and options
    categories = {
        'Name': ['Eric', 'Peter', 'Arnold'],
        'Drink': ['tea', 'water', 'milk'],
        'Nationality': ['dane', 'brit', 'swede'],
        'Education': ['high school', 'associate', 'bachelor'],
        'HouseStyle': ['victorian', 'colonial', 'ranch'],
        'Smoothie': ['cherry', 'watermelon', 'desert']
    }
    
    # Generate all possible permutations for each category
    name_perms = itertools.permutations(categories['Name'])
    drink_perms = itertools.permutations(categories['Drink'])
    nation_perms = itertools.permutations(categories['Nationality'])
    edu_perms = itertools.permutations(categories['Education'])
    style_perms = itertools.permutations(categories['HouseStyle'])
    smoothie_perms = itertools.permutations(categories['Smoothie'])
    
    # Iterate through all possible combinations
    for names in name_perms:
        for drinks in drink_perms:
            for nations in nation_perms:
                for educations in edu_perms:
                    for styles in style_perms:
                        for smoothies in smoothie_perms:
                            # Create a dictionary to represent the current assignment
                            assignment = {
                                1: {
                                    'Name': names[0],
                                    'Drink': drinks[0],
                                    'Nationality': nations[0],
                                    'Education': educations[0],
                                    'HouseStyle': styles[0],
                                    'Smoothie': smoothies[0]
                                },
                                2: {
                                    'Name': names[1],
                                    'Drink': drinks[1],
                                    'Nationality': nations[1],
                                    'Education': educations[1],
                                    'HouseStyle': styles[1],
                                    'Smoothie': smoothies[1]
                                },
                                3: {
                                    'Name': names[2],
                                    'Drink': drinks[2],
                                    'Nationality': nations[2],
                                    'Education': educations[2],
                                    'HouseStyle': styles[2],
                                    'Smoothie': smoothies[2]
                                }
                            }
                            
                            # Check all constraints
                            # Constraint 1: One house between Eric and the tea drinker
                            eric_pos = None
                            tea_pos = None
                            for house in [1, 2, 3]:
                                if assignment[house]['Name'] == 'Eric':
                                    eric_pos = house
                                if assignment[house]['Drink'] == 'tea':
                                    tea_pos = house
                            if eric_pos is None or tea_pos is None or abs(eric_pos - tea_pos) != 2:
                                continue
                            
                            # Constraint 2: Milk drinker is in ranch-style home
                            milk_ranch = True
                            for house in [1, 2, 3]:
                                if assignment[house]['Drink'] == 'milk' and assignment[house]['HouseStyle'] != 'ranch':
                                    milk_ranch = False
                                    break
                                if assignment[house]['HouseStyle'] == 'ranch' and assignment[house]['Drink'] != 'milk':
                                    milk_ranch = False
                                    break
                            if not milk_ranch:
                                continue
                            
                            # Constraint 3: Bachelor's degree is in house 2
                            if assignment[2]['Education'] != 'bachelor':
                                continue
                            
                            # Constraint 4: High school diploma is the Dane
                            high_school_dane = True
                            for house in [1, 2, 3]:
                                if assignment[house]['Education'] == 'high school' and assignment[house]['Nationality'] != 'dane':
                                    high_school_dane = False
                                    break
                                if assignment[house]['Nationality'] == 'dane' and assignment[house]['Education'] != 'high school':
                                    high_school_dane = False
                                    break
                            if not high_school_dane:
                                continue
                            
                            # Constraint 5: Desert smoothie lover is Swedish
                            desert_swede = True
                            for house in [1, 2, 3]:
                                if assignment[house]['Smoothie'] == 'desert' and assignment[house]['Nationality'] != 'swede':
                                    desert_swede = False
                                    break
                                if assignment[house]['Nationality'] == 'swede' and assignment[house]['Smoothie'] != 'desert':
                                    desert_swede = False
                                    break
                            if not desert_swede:
                                continue
                            
                            # Constraint 6: Victorian house is not in house 1
                            if assignment[1]['HouseStyle'] == 'victorian':
                                continue
                            
                            # Constraint 7: Cherry smoothie is in colonial-style house
                            cherry_colonial = True
                            for house in [1, 2, 3]:
                                if assignment[house]['Smoothie'] == 'cherry' and assignment[house]['HouseStyle'] != 'colonial':
                                    cherry_colonial = False
                                    break
                                if assignment[house]['HouseStyle'] == 'colonial' and assignment[house]['Smoothie'] != 'cherry':
                                    cherry_colonial = False
                                    break
                            if not cherry_colonial:
                                continue
                            
                            # Constraint 8: Arnold is to the right of Victorian house
                            victorian_pos = None
                            arnold_pos = None
                            for house in [1, 2, 3]:
                                if assignment[house]['HouseStyle'] == 'victorian':
                                    victorian_pos = house
                                if assignment[house]['Name'] == 'Arnold':
                                    arnold_pos = house
                            if victorian_pos is None or arnold_pos is None or arnold_pos <= victorian_pos:
                                continue
                            
                            # Constraint 9: Ranch-style home has high school diploma
                            ranch_high_school = True
                            for house in [1, 2, 3]:
                                if assignment[house]['HouseStyle'] == 'ranch' and assignment[house]['Education'] != 'high school':
                                    ranch_high_school = False
                                    break
                                if assignment[house]['Education'] == 'high school' and assignment[house]['HouseStyle'] != 'ranch':
                                    ranch_high_school = False
                                    break
                            if not ranch_high_school:
                                continue
                            
                            # If all constraints are satisfied, return the solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
                                    "rows": [
                                        ["1", assignment[1]['Name'], assignment[1]['Drink'], assignment[1]['Nationality'], assignment[1]['Education'], assignment[1]['HouseStyle'], assignment[1]['Smoothie']],
                                        ["2", assignment[2]['Name'], assignment[2]['Drink'], assignment[2]['Nationality'], assignment[2]['Education'], assignment[2]['HouseStyle'], assignment[2]['Smoothie']],
                                        ["3", assignment[3]['Name'], assignment[3]['Drink'], assignment[3]['Nationality'], assignment[3]['Education'], assignment[3]['HouseStyle'], assignment[3]['Smoothie']]
                                    ]
                                }
                            }
                            return json.dumps(solution, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())