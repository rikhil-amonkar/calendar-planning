import json
from itertools import permutations

def solve_puzzle():
    # Define all possible attributes
    names = ['Arnold', 'Eric']
    educations = ['associate', 'high school']
    heights = ['short', 'very short']
    foods = ['grilled cheese', 'pizza']
    drinks = ['tea', 'water']
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for edu_perm in permutations(educations):
            for height_perm in permutations(heights):
                for food_perm in permutations(foods):
                    for drink_perm in permutations(drinks):
                        # Create the house assignments
                        houses = [
                            {
                                'House': '1',
                                'Name': name_perm[0],
                                'Education': edu_perm[0],
                                'Height': height_perm[0],
                                'Food': food_perm[0],
                                'Drink': drink_perm[0]
                            },
                            {
                                'House': '2',
                                'Name': name_perm[1],
                                'Education': edu_perm[1],
                                'Height': height_perm[1],
                                'Food': food_perm[1],
                                'Drink': drink_perm[1]
                            }
                        ]
                        
                        # Check all constraints
                        # Clue 5: Arnold is the pizza lover
                        pizza_lover = None
                        for house in houses:
                            if house['Name'] == 'Arnold' and house['Food'] != 'pizza':
                                break
                        else:
                            # Check if Arnold is in one of the houses and has pizza
                            arnold_house = None
                            for house in houses:
                                if house['Name'] == 'Arnold':
                                    arnold_house = house
                                    break
                            if arnold_house is None or arnold_house['Food'] != 'pizza':
                                continue
                        
                        # Clue 1: The very short person is the pizza lover
                        for house in houses:
                            if house['Height'] == 'very short' and house['Food'] != 'pizza':
                                break
                        else:
                            pizza_house = None
                            for house in houses:
                                if house['Food'] == 'pizza':
                                    pizza_house = house
                                    break
                            if pizza_house is None or pizza_house['Height'] != 'very short':
                                continue
                        
                        # Clue 2: Grilled cheese is in house 2
                        if houses[1]['Food'] != 'grilled cheese':
                            continue
                        
                        # Clue 3: High school diploma is the pizza lover
                        for house in houses:
                            if house['Education'] == 'high school' and house['Food'] != 'pizza':
                                break
                        else:
                            pizza_house = None
                            for house in houses:
                                if house['Food'] == 'pizza':
                                    pizza_house = house
                                    break
                            if pizza_house is None or pizza_house['Education'] != 'high school':
                                continue
                        
                        # Clue 4: Tea drinker loves grilled cheese
                        for house in houses:
                            if house['Drink'] == 'tea' and house['Food'] != 'grilled cheese':
                                break
                        else:
                            grilled_cheese_house = None
                            for house in houses:
                                if house['Food'] == 'grilled cheese':
                                    grilled_cheese_house = house
                                    break
                            if grilled_cheese_house is None or grilled_cheese_house['Drink'] != 'tea':
                                continue
                        
                        # If all constraints are satisfied, return the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
                                "rows": [
                                    [
                                        houses[0]['House'],
                                        houses[0]['Name'],
                                        houses[0]['Education'],
                                        houses[0]['Height'],
                                        houses[0]['Food'],
                                        houses[0].get('Drink', houses[0].get('Drink', ''))  # Handle possible key difference
                                    ],
                                    [
                                        houses[1]['House'],
                                        houses[1]['Name'],
                                        houses[1]['Education'],
                                        houses[1]['Height'],
                                        houses[1]['Food'],
                                        houses[1]['Drink']
                                    ]
                                ]
                            }
                        }
                        return solution
    return {"solution": {"header": [], "rows": []}}

solution = solve_puzzle()
print(json.dumps(solution, indent=2))