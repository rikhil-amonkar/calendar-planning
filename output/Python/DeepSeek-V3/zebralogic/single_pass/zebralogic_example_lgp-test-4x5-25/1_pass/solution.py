import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3', '4']
    names = ['Arnold', 'Peter', 'Eric', 'Alice']
    house_styles = ['craftsman', 'colonial', 'victorian', 'ranch']
    hair_colors = ['red', 'blonde', 'black', 'brown']
    children = ['Bella', 'Fred', 'Meredith', 'Samantha']
    book_genres = ['mystery', 'fantasy', 'romance', 'science fiction']

    # Initialize possibilities for each house
    possibilities = []
    for house in houses:
        possibilities.append({
            'House': house,
            'Name': names.copy(),
            'HouseStyle': house_styles.copy(),
            'HairColor': hair_colors.copy(),
            'Children': children.copy(),
            'BookGenre': book_genres.copy()
        })

    # Apply constraints one by one
    # Constraint 1: Craftsman is in house 3
    for house in possibilities:
        if house['House'] == '3':
            house['HouseStyle'] = ['craftsman']
        else:
            house['HouseStyle'] = [style for style in house['HouseStyle'] if style != 'craftsman']

    # Constraint 7: Arnold has red hair
    for house in possibilities:
        if 'Arnold' in house['Name']:
            house['HairColor'] = ['red']
        if 'red' in house['HairColor']:
            house['Name'] = [name for name in house['Name'] if name == 'Arnold']

    # Constraint 12: Eric has black hair
    for house in possibilities:
        if 'Eric' in house['Name']:
            house['HairColor'] = ['black']
        if 'black' in house['HairColor']:
            house['Name'] = [name for name in house['Name'] if name == 'Eric']

    # Constraint 9: Black hair is in house 2
    for house in possibilities:
        if house['House'] == '2':
            house['HairColor'] = ['black']
            house['Name'] = ['Eric']
        else:
            house['HairColor'] = [color for color in house['HairColor'] if color != 'black']
            if 'Eric' in house['Name']:
                house['Name'].remove('Eric')

    # Constraint 13: Arnold loves science fiction
    for house in possibilities:
        if 'Arnold' in house['Name']:
            house['BookGenre'] = ['science fiction']
        if 'science fiction' in house['BookGenre']:
            house['Name'] = [name for name in house['Name'] if name == 'Arnold']

    # Constraint 10: Peter loves fantasy
    for house in possibilities:
        if 'Peter' in house['Name']:
            house['BookGenre'] = ['fantasy']
        if 'fantasy' in house['BookGenre']:
            house['Name'] = [name for name in house['Name'] if name == 'Peter']

    # Constraint 2: Alice loves romance
    for house in possibilities:
        if 'Alice' in house['Name']:
            house['BookGenre'] = ['romance']
        if 'romance' in house['BookGenre']:
            house['Name'] = [name for name in house['Name'] if name == 'Alice']

    # Constraint 8: Alice is in colonial house
    for house in possibilities:
        if 'Alice' in house['Name']:
            house['HouseStyle'] = ['colonial']
        if 'colonial' in house['HouseStyle']:
            house['Name'] = [name for name in house['Name'] if name == 'Alice']

    # Constraint 6: Peter's child is Bella
    for house in possibilities:
        if 'Peter' in house['Name']:
            house['Children'] = ['Bella']
        if 'Bella' in house['Children']:
            house['Name'] = [name for name in house['Name'] if name == 'Peter']

    # Constraint 11: Arnold's child is Meredith
    for house in possibilities:
        if 'Arnold' in house['Name']:
            house['Children'] = ['Meredith']
        if 'Meredith' in house['Children']:
            house['Name'] = [name for name in house['Name'] if name == 'Arnold']

    # Constraint 4: Child Samantha is in house 4
    for house in possibilities:
        if house['House'] == '4':
            house['Children'] = ['Samantha']
        else:
            house['Children'] = [child for child in house['Children'] if child != 'Samantha']

    # Constraint 3: Brown hair is in house 4
    for house in possibilities:
        if house['House'] == '4':
            house['HairColor'] = ['brown']
        else:
            house['HairColor'] = [color for color in house['HairColor'] if color != 'brown']

    # Constraint 5: Ranch is right of red hair (red is left of ranch)
    # Arnold has red hair (from constraint 7), so ranch must be to his right
    # Find Arnold's house
    arnold_house = None
    for house in possibilities:
        if 'Arnold' in house['Name']:
            arnold_house = int(house['House'])
            break
    if arnold_house:
        for house in possibilities:
            if int(house['House']) > arnold_house:
                house['HouseStyle'] = [style for style in house['HouseStyle'] if style != 'victorian' and style != 'colonial']
            else:
                house['HouseStyle'] = [style for style in house['HouseStyle'] if style != 'ranch']

    # Now assign remaining attributes by elimination
    # Assign house styles
    assigned_styles = set()
    for house in possibilities:
        if len(house['HouseStyle']) == 1:
            assigned_styles.add(house['HouseStyle'][0])
    for house in possibilities:
        if len(house['HouseStyle']) > 1:
            house['HouseStyle'] = [style for style in house['HouseStyle'] if style not in assigned_styles]

    # Assign names
    assigned_names = set()
    for house in possibilities:
        if len(house['Name']) == 1:
            assigned_names.add(house['Name'][0])
    for house in possibilities:
        if len(house['Name']) > 1:
            house['Name'] = [name for name in house['Name'] if name not in assigned_names]

    # Assign children
    assigned_children = set()
    for house in possibilities:
        if len(house['Children']) == 1:
            assigned_children.add(house['Children'][0])
    for house in possibilities:
        if len(house['Children']) > 1:
            house['Children'] = [child for child in house['Children'] if child not in assigned_children]

    # Assign book genres
    assigned_genres = set()
    for house in possibilities:
        if len(house['BookGenre']) == 1:
            assigned_genres.add(house['BookGenre'][0])
    for house in possibilities:
        if len(house['BookGenre']) > 1:
            house['BookGenre'] = [genre for genre in house['BookGenre'] if genre not in assigned_genres]

    # Assign hair colors
    assigned_colors = set()
    for house in possibilities:
        if len(house['HairColor']) == 1:
            assigned_colors.add(house['HairColor'][0])
    for house in possibilities:
        if len(house['HairColor']) > 1:
            house['HairColor'] = [color for color in house['HairColor'] if color not in assigned_colors]

    # Prepare the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
            "rows": []
        }
    }

    for house in sorted(possibilities, key=lambda x: int(x['House'])):
        row = [
            house['House'],
            house['Name'][0],
            house['HouseStyle'][0],
            house['HairColor'][0],
            house['Children'][0],
            house['BookGenre'][0]
        ]
        solution["solution"]["rows"].append(row)

    return json.dumps(solution)

print(solve_puzzle())