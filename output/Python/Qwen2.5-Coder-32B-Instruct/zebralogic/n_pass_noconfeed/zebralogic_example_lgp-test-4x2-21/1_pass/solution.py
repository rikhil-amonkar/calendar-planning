import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    houses = [1, 2, 3, 4]
    names = ['Eric', 'Arnold', 'Alice', 'Peter']
    house_styles = ['craftsman', 'colonial', 'ranch', 'victorian']

    # Generate all possible permutations for the assignments
    for name_perm in itertools.permutations(names):
        for style_perm in itertools.permutations(house_styles):
            # Unpack the permutations for easier reference
            name_to_house = {name: i + 1 for i, name in enumerate(name_perm)}
            style_to_house = {style: i + 1 for i, style in enumerate(style_perm)}

            # Check the clues
            if (name_to_house['Alice'] == 2 and
                style_to_house['victorian'] + 1 == name_to_house['Peter'] and
                style_to_house['ranch'] < name_to_house['Peter'] and
                style_to_house['craftsman'] < name_to_house['Arnold'] and
                style_to_house['craftsman'] == name_to_house['Alice']):
                
                # If all clues are satisfied, construct the solution
                solution_rows = []
                for house in houses:
                    name = next(n for n, h in name_to_house.items() if h == house)
                    style = next(s for s, h in style_to_house.items() if h == house)
                    solution_rows.append([str(house), name, style])

                solution = {
                    "solution": {
                        "header": ["House", "Name", "HouseStyle"],
                        "rows": solution_rows
                    }
                }

                return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())