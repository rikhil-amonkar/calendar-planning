import itertools
import json

def solve_puzzle():
    # Define all possible categories and their options
    categories = {
        'House': ['1', '2', '3'],
        'Name': ['Eric', 'Peter', 'Arnold'],
        'Drink': ['tea', 'water', 'milk'],
        'Nationality': ['dane', 'brit', 'swede'],
        'Education': ['high school', 'associate', 'bachelor'],
        'House Style': ['victorian', 'colonial', 'ranch'],
        'Smoothie': ['cherry', 'watermelon', 'desert']
    }
    
    # Generate all possible permutations for each category
    for name_order in itertools.permutations(categories['Name']):
        for drink_order in itertools.permutations(categories['Drink']):
            for nationality_order in itertools.permutations(categories['Nationality']):
                for education_order in itertools.permutations(categories['Education']):
                    for house_style_order in itertools.permutations(categories['House Style']):
                        for smoothie_order in itertools.permutations(categories['Smoothie']):
                            # Create a list of houses with their attributes
                            houses = []
                            for i in range(3):
                                house = {
                                    'House': str(i+1),
                                    'Name': name_order[i],
                                    'Drink': drink_order[i],
                                    'Nationality': nationality_order[i],
                                    'Education': education_order[i],
                                    'House Style': house_style_order[i],
                                    'Smoothie': smoothie_order[i]
                                }
                                houses.append(house)
                            
                            # Check all constraints
                            valid = True
                            
                            # Clue 1: One house between Eric and the tea drinker
                            eric_pos = None
                            tea_pos = None
                            for i, house in enumerate(houses):
                                if house['Name'] == 'Eric':
                                    eric_pos = i + 1  # 1-based
                                if house['Drink'] == 'tea':
                                    tea_pos = i + 1
                            if eric_pos is None or tea_pos is None or abs(eric_pos - tea_pos) != 2:
                                valid = False
                            
                            # Clue 2: Milk drinker is in ranch-style home
                            for house in houses:
                                if house['Drink'] == 'milk' and house['House Style'] != 'ranch':
                                    valid = False
                                if house['House Style'] == 'ranch' and house['Drink'] != 'milk':
                                    valid = False
                            
                            # Clue 3: Bachelor's degree is in house 2
                            if houses[1]['Education'] != 'bachelor':
                                valid = False
                            
                            # Clue 4: High school diploma is the Dane
                            for house in houses:
                                if house['Education'] == 'high school' and house['Nationality'] != 'dane':
                                    valid = False
                                if house['Nationality'] == 'dane' and house['Education'] != 'high school':
                                    valid = False
                            
                            # Clue 5: Desert smoothie lover is Swedish
                            for house in houses:
                                if house['Smoothie'] == 'desert' and house['Nationality'] != 'swede':
                                    valid = False
                                if house['Nationality'] == 'swede' and house['Smoothie'] != 'desert':
                                    valid = False
                            
                            # Clue 6: Victorian house is not first
                            if houses[0]['House Style'] == 'victorian':
                                valid = False
                            
                            # Clue 7: Cherry smoothie is in colonial house
                            for house in houses:
                                if house['Smoothie'] == 'cherry' and house['House Style'] != 'colonial':
                                    valid = False
                                if house['House Style'] == 'colonial' and house['Smoothie'] != 'cherry':
                                    valid = False
                            
                            # Clue 8: Arnold is right of Victorian house
                            victorian_pos = None
                            arnold_pos = None
                            for i, house in enumerate(houses):
                                if house['House Style'] == 'victorian':
                                    victorian_pos = i + 1
                                if house['Name'] == 'Arnold':
                                    arnold_pos = i + 1
                            if victorian_pos is None or arnold_pos is None or arnold_pos <= victorian_pos:
                                valid = False
                            
                            # Clue 9: Ranch-style home has high school diploma
                            for house in houses:
                                if house['House Style'] == 'ranch' and house['Education'] != 'high school':
                                    valid = False
                                if house['Education'] == 'high school' and house['House Style'] != 'ranch':
                                    valid = False
                            
                            if valid:
                                # Prepare the solution in the required format
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Drink", "Nationality", "Education", "House Style", "Smoothie"],
                                        "rows": []
                                    }
                                }
                                for house in houses:
                                    row = [
                                        house['House'],
                                        house['Name'],
                                        house['Drink'],
                                        house['Nationality'],
                                        house['Education'],
                                        house['House Style'],
                                        house['Smoothie']
                                    ]
                                    solution["solution"]["rows"].append(row)
                                return solution
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))