import json

def solve_puzzle():
    # Define the possible values for each attribute
    houses = ['1', '2']
    names = ['Eric', 'Arnold']
    house_styles = ['victorian', 'colonial']

    # Initialize the solution list
    solution = []

    # Iterate over all possible permutations
    for name1 in names:
        for style1 in house_styles:
            for name2 in names:
                if name2 != name1:  # Ensure different people in different houses
                    for style2 in house_styles:
                        if style2 != style1:  # Ensure different styles in different houses
                            # Check the clues
                            if style1 == 'victorian' and style2 == 'colonial' and name1 == 'Eric':
                                solution.append([houses[0], name1, style1])
                                solution.append([houses[1], name2, style2])

    # Format the solution as JSON
    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": solution
        }
    }

    return json.dumps(result, indent=4)

# Print the solution
print(solve_puzzle())