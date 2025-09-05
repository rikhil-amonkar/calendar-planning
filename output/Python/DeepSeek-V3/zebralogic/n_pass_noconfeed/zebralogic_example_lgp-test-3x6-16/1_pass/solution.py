import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Eric', 'Peter', 'Arnold']
    drinks = ['tea', 'water', 'milk']
    nationalities = ['dane', 'brit', 'swede']
    educations = ['high school', 'associate', 'bachelor']
    house_styles = ['victorian', 'colonial', 'ranch']
    smoothies = ['cherry', 'watermelon', 'desert']
    
    houses = [1, 2, 3]
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for drink_perm in permutations(drinks):
            for nation_perm in permutations(nationalities):
                for edu_perm in permutations(educations):
                    for style_perm in permutations(house_styles):
                        for smoothie_perm in permutations(smoothies):
                            # Create assignment for each house
                            assignment = []
                            for i in range(3):
                                house = {
                                    'house': i+1,
                                    'name': name_perm[i],
                                    'drink': drink_perm[i],
                                    'nationality': nation_perm[i],
                                    'education': edu_perm[i],
                                    'house_style': style_perm[i],
                                    'smoothie': smoothie_perm[i]
                                }
                                assignment.append(house)
                            
                            # Check all constraints
                            valid = True
                            
                            # Clue 1: One house between Eric and the tea drinker
                            eric_house = None
                            tea_house = None
                            for house in assignment:
                                if house['name'] == 'Eric':
                                    eric_house = house['house']
                                if house['drink'] == 'tea':
                                    tea_house = house['house']
                            
                            if eric_house is None or tea_house is None or abs(eric_house - tea_house) != 2:
                                valid = False
                                continue
                            
                            # Clue 2: Milk drinker is in ranch-style home
                            for house in assignment:
                                if house['drink'] == 'milk' and house['house_style'] != 'ranch':
                                    valid = False
                                    break
                                if house['house_style'] == 'ranch' and house['drink'] != 'milk':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 3: Bachelor's degree in second house
                            if assignment[1]['education'] != 'bachelor':
                                valid = False
                                continue
                            
                            # Clue 4: High school diploma is the Dane
                            for house in assignment:
                                if house['education'] == 'high school' and house['nationality'] != 'dane':
                                    valid = False
                                    break
                                if house['nationality'] == 'dane' and house['education'] != 'high school':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 5: Desert smoothie lover is Swedish
                            for house in assignment:
                                if house['smoothie'] == 'desert' and house['nationality'] != 'swede':
                                    valid = False
                                    break
                                if house['nationality'] == 'swede' and house['smoothie'] != 'desert':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 6: Victorian house not in first house
                            if assignment[0]['house_style'] == 'victorian':
                                valid = False
                                continue
                            
                            # Clue 7: Cherry smoothie lover in colonial-style house
                            for house in assignment:
                                if house['smoothie'] == 'cherry' and house['house_style'] != 'colonial':
                                    valid = False
                                    break
                                if house['house_style'] == 'colonial' and house['smoothie'] != 'cherry':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 8: Arnold is right of Victorian house
                            victorian_house = None
                            arnold_house = None
                            for house in assignment:
                                if house['house_style'] == 'victorian':
                                    victorian_house = house['house']
                                if house['name'] == 'Arnold':
                                    arnold_house = house['house']
                            
                            if victorian_house is None or arnold_house is None or arnold_house <= victorian_house:
                                valid = False
                                continue
                            
                            # Clue 9: Ranch-style home has high school diploma
                            for house in assignment:
                                if house['house_style'] == 'ranch' and house['education'] != 'high school':
                                    valid = False
                                    break
                                if house['education'] == 'high school' and house['house_style'] != 'ranch':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # If we get here, all constraints are satisfied
                            if valid:
                                # Format the solution
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
                                        "rows": []
                                    }
                                }
                                
                                for house in sorted(assignment, key=lambda x: x['house']):
                                    row = [
                                        str(house['house']),
                                        house['name'],
                                        house['drink'],
                                        house['nationality'],
                                        house['education'],
                                        house['house_style'],
                                        house['smoothie']
                                    ]
                                    solution["solution"]["rows"].append(row)
                                
                                print(json.dumps(solution, indent=2))
                                return
    
    print('{"solution": {"header": [], "rows": []}}')

if __name__ == "__main__":
    main()