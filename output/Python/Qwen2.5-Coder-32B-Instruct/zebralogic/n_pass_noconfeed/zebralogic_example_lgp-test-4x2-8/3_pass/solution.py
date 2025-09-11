import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    houses = [1, 2, 3, 4]
    names = ['Peter', 'Arnold', 'Alice', 'Eric']
    colors = ['yellow', 'green', 'red', 'white']

    # Generate all possible permutations for names and colors
    for name_perm in itertools.permutations(names):
        for color_perm in itertools.permutations(colors):
            # Create a dictionary to store the current permutation
            solution = {house: {'name': name, 'color': color} 
                        for house, name, color in zip(houses, name_perm, color_perm)}

            # Check each clue
            if (solution[3]['color'] == 'green' and  # Clue 1
                solution[1]['name'] == 'Peter' and   # Clue 2
                abs(houses[colors.index('red')] - houses[colors.index('yellow')]) == 2 and  # Clue 3
                (solution[1]['name'] == 'Peter' and solution[2]['name'] == 'Eric' or  # Clue 4
                 solution[2]['name'] == 'Peter' and solution[1]['name'] == 'Eric' or
                 solution[2]['name'] == 'Peter' and solution[3]['name'] == 'Eric' or
                 solution[3]['name'] == 'Peter' and solution[2]['name'] == 'Eric') and
                solution[names.index('Eric') + 1]['color'] == 'yellow'):  # Clue 5

                # Format the solution as required
                formatted_solution = {
                    "solution": {
                        "header": ["House", "Name", "Color"],
                        "rows": [[str(house), solution[house]['name'], solution[house]['color']] for house in houses]
                    }
                }

                # Output the solution as JSON
                print(json.dumps(formatted_solution, indent=2))
                return

# Run the function to solve the puzzle
solve_puzzle()