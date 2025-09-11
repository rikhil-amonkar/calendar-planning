import itertools
import json

def solve_puzzle():
    # Define the possible values for each characteristic
    names = ['Arnold', 'Peter', 'Eric']
    heights = ['short', 'average', 'very short']
    houses = [1, 2, 3]

    # Generate all possible permutations for names and heights
    name_permutations = list(itertools.permutations(names))
    height_permutations = list(itertools.permutations(heights))

    # Iterate over all combinations of name and height permutations
    for name_order in name_permutations:
        for height_order in height_permutations:
            # Create a dictionary to map each house to its attributes
            house_attributes = {house: {'name': name, 'height': height}
                                for house, name, height in zip(houses, name_order, height_order)}

            # Check the constraints
            if (house_attributes[2]['name'] == 'Peter' and house_attributes[1]['name'] == 'Eric') or \
               (house_attributes[3]['name'] == 'Peter' and house_attributes[1]['name'] == 'Eric') or \
               (house_attributes[3]['name'] == 'Peter' and house_attributes[2]['name'] == 'Eric'):
                if house_attributes[1]['height'] == 'short':
                    if abs(list(house_attributes.keys())[list(house_attributes.values()).index({'height': 'short'})] -
                             list(house_attributes.keys())[list(house_attributes.values()).index({'height': 'very short'})]) == 2:
                        if abs(list(house_attributes.keys())[list(house_attributes.values()).index({'name': 'Arnold'})] -
                                 list(house_attributes.keys())[list(house_attributes.values()).index({'height': 'very short'})]) == 1:
                            # If all constraints are satisfied, format the solution
                            solution_rows = [[str(house), attributes['name'], attributes['height']]
                                             for house, attributes in house_attributes.items()]
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Height"],
                                    "rows": solution_rows
                                }
                            }
                            return json.dumps(solution, indent=2)

# Print the solution
print(solve_puzzle())