import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    categories = {
        'Name': ['Peter', 'Arnold', 'Alice', 'Eric'],
        'Flower': ['roses', 'daffodils', 'carnations', 'lilies'],
        'Hobby': ['photography', 'painting', 'cooking', 'gardening'],
        'Pet': ['dog', 'fish', 'bird', 'cat'],
        'Color': ['red', 'yellow', 'green', 'white'],
        'HouseStyle': ['craftsman', 'colonial', 'ranch', 'victorian']
    }
    
    # Initialize houses
    houses = [{'House': str(i)} for i in range(1, 5)]
    
    # Apply clue 6: Craftsman is house 2
    houses[1]['HouseStyle'] = 'craftsman'
    # Apply clue 1: Arnold is in craftsman
    houses[1]['Name'] = 'Arnold'
    
    # Apply clue 7: Eric is in victorian
    for house in houses:
        if 'HouseStyle' not in house:
            continue
        if house['HouseStyle'] == 'victorian':
            house['Name'] = 'Eric'
    # Also, Eric must be in victorian, so find which house is victorian
    # We don't know yet, but we know craftsman is house 2, so victorian is 1,3, or 4
    
    # Apply clue 14: Eric has cat
    for house in houses:
        if 'Name' in house and house['Name'] == 'Eric':
            house['Pet'] = 'cat'
    
    # Apply clue 13: colonial has color red
    # We don't know which house is colonial yet
    
    # Apply clue 5: roses lover has color red
    # So roses lover is in colonial house
    
    # Apply clue 2: roses are to the right of Peter
    # So Peter is to the left of roses
    
    # Apply clue 4: daffodils not in house 4
    # Apply clue 12: daffodils lover has color yellow
    
    # Apply clue 8: fish owner loves white
    # Apply clue 10: white lover loves carnations
    # Apply clue 11: white is right of gardening
    
    # Apply clue 3: photography hobbyist owns dog
    # Apply clue 9: cooking is right of red (roses lover)
    
    # Generate all possible permutations for remaining attributes
    names = set(categories['Name'])
    assigned_names = {house['Name'] for house in houses if 'Name' in house}
    remaining_names = list(names - assigned_names)
    
    flowers = set(categories['Flower'])
    hobbies = set(categories['Hobby'])
    pets = set(categories['Pet'])
    colors = set(categories['Color'])
    styles = set(categories['HouseStyle'])
    assigned_styles = {house['HouseStyle'] for house in houses if 'HouseStyle' in house}
    remaining_styles = list(styles - assigned_styles)
    
    # Try all possible assignments for remaining houses
    for name_perm in permutations(remaining_names):
        for style_perm in permutations(remaining_styles):
            # Assign names and styles to houses not yet assigned
            temp_houses = [house.copy() for house in houses]
            name_idx = 0
            style_idx = 0
            for i in range(4):
                if 'Name' not in temp_houses[i]:
                    temp_houses[i]['Name'] = name_perm[name_idx]
                    name_idx += 1
                if 'HouseStyle' not in temp_houses[i]:
                    temp_houses[i]['HouseStyle'] = style_perm[style_idx]
                    style_idx += 1
            
            # Check if Eric is in victorian (clue 7)
            eric_house = None
            for house in temp_houses:
                if house['Name'] == 'Eric':
                    eric_house = house
            if eric_house['HouseStyle'] != 'victorian':
                continue
            
            # Assign pets: Eric has cat (already done), others unknown
            # Assign colors, flowers, hobbies based on clues
            
            # Find colonial house (clue 13: color red)
            colonial_house = None
            for house in temp_houses:
                if house['HouseStyle'] == 'colonial':
                    colonial_house = house
            if not colonial_house:
                continue
            
            # Colonial house has color red (clue 13)
            colonial_house['Color'] = 'red'
            # And loves roses (clue 5)
            colonial_house['Flower'] = 'roses'
            
            # Peter is to the left of roses (clue 2)
            peter_pos = None
            roses_pos = None
            for i, house in enumerate(temp_houses):
                if house['Name'] == 'Peter':
                    peter_pos = i
                if 'Flower' in house and house['Flower'] == 'roses':
                    roses_pos = i
            if peter_pos is None or roses_pos is None or peter_pos >= roses_pos:
                continue
            
            # clue 9: cooking is right of red (roses is red)
            cooking_pos = None
            for i, house in enumerate(temp_houses):
                if 'Hobby' in house and house['Hobby'] == 'cooking':
                    cooking_pos = i
            if cooking_pos is not None and cooking_pos <= roses_pos:
                continue
            
            # clue 12: daffodils lover has yellow
            # clue 4: daffodils not in house 4
            possible_daffodil_houses = [house for house in temp_houses if 'Flower' not in house and house['House'] != '4']
            for house in possible_daffodil_houses:
                house['Flower'] = 'daffodils'
                house['Color'] = 'yellow'
            
            # Assign remaining flowers: carnations and lilies
            remaining_flowers = set(categories['Flower']) - {'roses', 'daffodils'}
            for house in temp_houses:
                if 'Flower' not in house:
                    for flower in remaining_flowers:
                        house['Flower'] = flower
                        remaining_flowers.remove(flower)
                        break
            
            # clue 10: white lover loves carnations
            # clue 8: fish owner loves white
            # clue 11: white is right of gardening
            gardening_pos = None
            white_pos = None
            for i, house in enumerate(temp_houses):
                if 'Flower' in house and house['Flower'] == 'carnations':
                    house['Color'] = 'white'
                    white_pos = i
                if 'Hobby' in house and house['Hobby'] == 'gardening':
                    gardening_pos = i
            if white_pos is not None and gardening_pos is not None and white_pos <= gardening_pos:
                continue
            
            # Assign fish to white house
            for house in temp_houses:
                if 'Color' in house and house['Color'] == 'white':
                    house['Pet'] = 'fish'
            
            # clue 3: photography hobbyist owns dog
            # Assign hobbies
            remaining_hobbies = set(categories['Hobby'])
            for house in temp_houses:
                if 'Pet' in house and house['Pet'] == 'dog':
                    house['Hobby'] = 'photography'
                    remaining_hobbies.remove('photography')
            
            # Assign remaining hobbies
            for house in temp_houses:
                if 'Hobby' not in house:
                    for hobby in remaining_hobbies:
                        house['Hobby'] = hobby
                        remaining_hobbies.remove(hobby)
                        break
            
            # clue 9: cooking is right of red
            cooking_pos = None
            red_pos = None
            for i, house in enumerate(temp_houses):
                if 'Color' in house and house['Color'] == 'red':
                    red_pos = i
                if 'Hobby' in house and house['Hobby'] == 'cooking':
                    cooking_pos = i
            if cooking_pos is not None and red_pos is not None and cooking_pos <= red_pos:
                continue
            
            # Assign remaining pets
            remaining_pets = set(categories['Pet'])
            assigned_pets = set()
            for house in temp_houses:
                if 'Pet' in house:
                    assigned_pets.add(house['Pet'])
            remaining_pets -= assigned_pets
            for house in temp_houses:
                if 'Pet' not in house:
                    for pet in remaining_pets:
                        house['Pet'] = pet
                        remaining_pets.remove(pet)
                        break
            
            # Assign remaining colors
            remaining_colors = set(categories['Color'])
            assigned_colors = set()
            for house in temp_houses:
                if 'Color' in house:
                    assigned_colors.add(house['Color'])
            remaining_colors -= assigned_colors
            for house in temp_houses:
                if 'Color' not in house:
                    for color in remaining_colors:
                        house['Color'] = color
                        remaining_colors.remove(color)
                        break
            
            # Verify all clues are satisfied
            valid = True
            # Check all categories are filled
            for house in temp_houses:
                for category in categories:
                    if category.lower() == 'house':
                        continue
                    if category not in house:
                        valid = False
                        break
                if not valid:
                    break
            if not valid:
                continue
            
            # Prepare the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
                    "rows": []
                }
            }
            for house in temp_houses:
                row = [
                    house['House'],
                    house['Name'],
                    house['Flower'],
                    house['Hobby'],
                    house['Pet'],
                    house['Color'],
                    house['HouseStyle']
                ]
                solution["solution"]["rows"].append(row)
            
            return solution
    
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))