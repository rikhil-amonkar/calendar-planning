import itertools
import json

def solve_puzzle():
    # Define the possible values for each characteristic
    names = ["Peter", "Arnold", "Alice", "Eric"]
    colors = ["yellow", "green", "red", "white"]
    houses = [1, 2, 3, 4]

    # Generate all possible permutations for names and colors
    all_permutations = list(itertools.permutations(names)) * list(itertools.permutations(colors))

    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(name_perm, color_perm):
        # Unpack the permutations into a list of tuples (house, name, color)
        solution = list(zip(houses, name_perm, color_perm))
        
        # Check each clue
        # Clue 1: The person whose favorite color is green is in the third house.
        if not any(person[2] == "green" and person[0] == 3 for person in solution):
            return False
        
        # Clue 2: Peter is in the first house.
        if not any(person[1] == "Peter" and person[0] == 1 for person in solution):
            return False
        
        # Clue 3: There is one house between the person whose favorite color is red and the person who loves yellow.
        red_house = next((person[0] for person in solution if person[2] == "red"), None)
        yellow_house = next((person[0] for person in solution if person[2] == "yellow"), None)
        if abs(red_house - yellow_house) != 2:
            return False
        
        # Clue 4: Arnold is directly left of Eric.
        arnold_house = next((person[0] for person in solution if person[1] == "Arnold"), None)
        eric_house = next((person[0] for person in solution if person[1] == "Eric"), None)
        if arnold_house + 1 != eric_house:
            return False
        
        # Clue 5: Eric is the person who loves yellow.
        if not any(person[1] == "Eric" and person[2] == "yellow" for person in solution):
            return False
        
        return True

    # Find the valid solution
    for name_perm in itertools.permutations(names):
        for color_perm in itertools.permutations(colors):
            if is_valid_solution(name_perm, color_perm):
                solution = list(zip(houses, name_perm, color_perm))
                break

    # Format the solution as JSON
    result = {
        "solution": {
            "header": ["House", "Name", "Color"],
            "rows": [[str(house), name, color] for house, name, color in solution]
        }
    }

    # Output the solution as JSON
    print(json.dumps(result, indent=2))

# Run the function to solve the puzzle
solve_puzzle()