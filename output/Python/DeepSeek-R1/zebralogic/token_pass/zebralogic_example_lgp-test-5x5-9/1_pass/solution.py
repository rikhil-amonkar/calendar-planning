import itertools
import json

def main():
    # Define the attributes
    names = ['Bob', 'Arnold', 'Peter', 'Alice', 'Eric']
    drinks = ['milk', 'root beer', 'coffee', 'tea', 'water']
    colors = ['blue', 'green', 'white', 'yellow', 'red']
    flowers = ['daffodils', 'roses', 'lilies', 'tulips', 'carnations']
    hobbies = ['painting', 'cooking', 'photography', 'gardening', 'knitting']
    
    # Fixed assignments from clues
    fixed_assignments = [
        {'name': None, 'drink': 'root beer', 'color': None, 'flower': 'carnations', 'hobby': 'gardening'},  # house0
        {'name': None, 'drink': None, 'color': 'white', 'flower': 'roses', 'hobby': None},  # house1
        {'name': 'Peter', 'drink': 'water', 'color': 'red', 'flower': None, 'hobby': None},  # house2
        {'name': None, 'drink': None, 'color': None, 'flower': None, 'hobby': None},  # house3
        {'name': None, 'drink': None, 'color': None, 'flower': None, 'hobby': None}   # house4
    ]
    
    # Generate all possible assignments for the missing values
    # Names: for house0, house1, house3, house4, but house3 cannot be Alice
    name_values = [n for n in names if n != 'Peter']
    name_perms = list(itertools.permutations(name_values))
    # Filter out assignments where house3 (index2 in the tuple) is 'Alice'
    name_perms = [p for p in name_perms if p[2] != 'Alice']
    
    # Drinks: for house1, house3, house4 (milk, coffee, tea)
    drink_values = ['milk', 'coffee', 'tea']
    drink_perms = list(itertools.permutations(drink_values))
    
    # Colors: for house0, house3, house4. But green must be in house3 or house4.
    color_options = []
    for green_house in [3,4]:
        other_houses = [0,3,4]
        other_houses.remove(green_house)
        other_colors = ['blue', 'yellow']
        for perm in itertools.permutations(other_colors):
            color_assignment = [None] * 5
            color_assignment[green_house] = 'green'
            for i, house in enumerate(other_houses):
                color_assignment[house] = perm[i]
            color_options.append(color_assignment)
    
    # Flowers: for house2, house3, house4 (daffodils, lilies, tulips)
    flower_values = ['daffodils', 'lilies', 'tulips']
    flower_perms = list(itertools.permutations(flower_values))
    
    # Hobbies: for house1, house2, house3, house4 (painting, cooking, photography, knitting)
    hobby_values = ['painting', 'cooking', 'photography', 'knitting']
    hobby_perms = list(itertools.permutations(hobby_values))
    
    # Now, iterate over all combinations
    for name_perm in name_perms:
        for drink_perm in drink_perms:
            for color_perm in color_options:
                for flower_perm in flower_perms:
                    for hobby_perm in hobby_perms:
                        # Create a copy of the fixed assignments
                        houses = [dict(house) for house in fixed_assignments]
                        
                        # Assign names
                        houses[0]['name'] = name_perm[0]
                        houses[1]['name'] = name_perm[1]
                        houses[3]['name'] = name_perm[2]
                        houses[4]['name'] = name_perm[3]
                        
                        # Assign drinks
                        houses[1]['drink'] = drink_perm[0]
                        houses[3]['drink'] = drink_perm[1]
                        houses[4]['drink'] = drink_perm[2]
                        
                        # Assign colors
                        houses[0]['color'] = color_perm[0]
                        houses[3]['color'] = color_perm[3]
                        houses[4]['color'] = color_perm[4]
                        
                        # Assign flowers
                        houses[2]['flower'] = flower_perm[0]
                        houses[3]['flower'] = flower_perm[1]
                        houses[4]['flower'] = flower_perm[2]
                        
                        # Assign hobbies
                        houses[1]['hobby'] = hobby_perm[0]
                        houses[2]['hobby'] = hobby_perm[1]
                        houses[3]['hobby'] = hobby_perm[2]
                        houses[4]['hobby'] = hobby_perm[3]
                        
                        # Check constraints
                        if check_constraints(houses):
                            # Output the solution
                            output_solution(houses)
                            return

def check_constraints(houses):
    # Clue 3: green color is coffee drinker
    for i in range(5):
        if houses[i]['color'] == 'green':
            if houses[i]['drink'] != 'coffee':
                return False
        if houses[i]['drink'] == 'coffee':
            if houses[i]['color'] != 'green':
                return False
                
    # Clue 4: green color is lilies
    for i in range(5):
        if houses[i]['color'] == 'green':
            if houses[i]['flower'] != 'lilies':
                return False
        if houses[i]['flower'] == 'lilies':
            if houses[i]['color'] != 'green':
                return False
                
    # Clue 5: blue color is right of daffodils
    blue_house = None
    daffodils_house = None
    for i in range(5):
        if houses[i]['color'] == 'blue':
            blue_house = i
        if houses[i]['flower'] == 'daffodils':
            daffodils_house = i
    if blue_house is None or daffodils_house is None or blue_house <= daffodils_house:
        return False
        
    # Clue 6: cooking is blue
    for i in range(5):
        if houses[i]['hobby'] == 'cooking':
            if houses[i]['color'] != 'blue':
                return False
        if houses[i]['color'] == 'blue':
            if houses[i]['hobby'] != 'cooking':
                return False
                
    # Clue 7: Eric is directly left of tea drinker
    eric_house = None
    tea_house = None
    for i in range(5):
        if houses[i]['name'] == 'Eric':
            eric_house = i
        if houses[i]['drink'] == 'tea':
            tea_house = i
    if eric_house is None or tea_house is None or eric_house != tea_house - 1:
        return False
        
    # Clue 9: Arnold is photography
    for i in range(5):
        if houses[i]['name'] == 'Arnold':
            if houses[i]['hobby'] != 'photography':
                return False
        if houses[i]['hobby'] == 'photography':
            if houses[i]['name'] != 'Arnold':
                return False
                
    # Clue 12: cooking is left of painting
    cooking_house = None
    painting_house = None
    for i in range(5):
        if houses[i]['hobby'] == 'cooking':
            cooking_house = i
        if houses[i]['hobby'] == 'painting':
            painting_house = i
    if cooking_house is None or painting_house is None or cooking_house >= painting_house:
        return False
        
    return True

def output_solution(houses):
    solution = {
        "solution": {
            "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
            "rows": []
        }
    }
    for i in range(5):
        house = houses[i]
        row = [
            str(i+1),
            house['name'],
            house['drink'],
            house['color'],
            house['flower'],
            house['hobby']
        ]
        solution["solution"]["rows"].append(row)
    
    print(json.dumps(solution, indent=2))

if __name__ == '__main__':
    main()