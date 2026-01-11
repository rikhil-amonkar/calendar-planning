import json

def solve_puzzle():
    # Initialize possible values for each attribute
    names = ['Arnold', 'Eric']
    educations = ['associate', 'high school']
    heights = ['short', 'very short']
    foods = ['grilled cheese', 'pizza']
    drinks = ['tea', 'water']

    # Initialize houses with all possible values
    house1 = {'Name': set(names), 'Education': set(educations), 'Height': set(heights), 'Food': set(foods), 'Drink': set(drinks)}
    house2 = {'Name': set(names), 'Education': set(educations), 'Height': set(heights), 'Food': set(foods), 'Drink': set(drinks)}

    # Apply Clue 1: The person who is very short is the person who is a pizza lover.
    if 'very short' in house1['Height'] and 'pizza' in house1['Food']:
        house1['Height'] = {'very short'}
        house1['Food'] = {'pizza'}
    elif 'very short' in house2['Height'] and 'pizza' in house2['Food']:
        house2['Height'] = {'very short'}
        house2['Food'] = {'pizza'}

    # Apply Clue 2: The person who loves eating grilled cheese is in the second house.
    house2['Food'] = {'grilled cheese'}
    house1['Food'].discard('grilled cheese')

    # Apply Clue 3: The person with a high school diploma is the person who is a pizza lover.
    if 'high school' in house1['Education'] and 'pizza' in house1['Food']:
        house1['Education'] = {'high school'}
        house1['Food'] = {'pizza'}
    elif 'high school' in house2['Education'] and 'pizza' in house2['Food']:
        house2['Education'] = {'high school'}
        house2['Food'] = {'pizza'}

    # Apply Clue 4: The tea drinker is the person who loves eating grilled cheese.
    if 'tea' in house1['Drink'] and 'grilled cheese' in house1['Food']:
        house1['Drink'] = {'tea'}
        house1['Food'] = {'grilled cheese'}
    elif 'tea' in house2['Drink'] and 'grilled cheese' in house2['Food']:
        house2['Drink'] = {'tea'}
        house2['Food'] = {'grilled cheese'}

    # Apply Clue 5: Arnold is the person who is a pizza lover.
    if 'Arnold' in house1['Name'] and 'pizza' in house1['Food']:
        house1['Name'] = {'Arnold'}
        house1['Food'] = {'pizza'}
    elif 'Arnold' in house2['Name'] and 'pizza' in house2['Food']:
        house2['Name'] = {'Arnold'}
        house2['Food'] = {'pizza'}

    # Eliminate conflicts and finalize assignments
    # Since Arnold is the pizza lover and he is very short (from Clue 1 and Clue 5)
    if 'Arnold' in house1['Name']:
        house1['Name'] = {'Arnold'}
        house1['Height'] = {'very short'}
        house1['Food'] = {'pizza'}
        house1['Education'] = {'high school'}  # From Clue 3
        house1['Drink'] = {'water'}  # By elimination
        house2['Name'] = {'Eric'}
        house2['Height'] = {'short'}
        house2['Food'] = {'grilled cheese'}
        house2['Education'] = {'associate'}
        house2['Drink'] = {'tea'}
    else:
        house2['Name'] = {'Arnold'}
        house2['Height'] = {'very short'}
        house2['Food'] = {'pizza'}
        house2['Education'] = {'high school'}  # From Clue 3
        house2['Drink'] = {'water'}  # By elimination
        house1['Name'] = {'Eric'}
        house1['Height'] = {'short'}
        house1['Food'] = {'grilled cheese'}
        house1['Education'] = {'associate'}
        house1['Drink'] = {'tea'}

    # Prepare the solution in the required JSON format
    solution = {
        "solution": {
            "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
            "rows": [
                ["1", next(iter(house1['Name'])), next(iter(house1['Education'])), next(iter(house1['Height'])), next(iter(house1['Food'])), next(iter(house1['Drink']))],
                ["2", next(iter(house2['Name'])), next(iter(house2['Education'])), next(iter(house2['Height'])), next(iter(house2['Food'])), next(iter(house2['Drink']))]
            ]
        }
    }

    return json.dumps(solution, indent=2)

# Run the function and print the result
print(solve_puzzle())