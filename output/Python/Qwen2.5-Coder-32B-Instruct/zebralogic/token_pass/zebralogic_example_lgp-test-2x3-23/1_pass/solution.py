import json

def solve_puzzle():
    # Initialize possible assignments
    people = ['Eric', 'Arnold']
    children = ['Bella', 'Fred']
    foods = ['grilled cheese', 'pizza']
    
    # Based on the clues, we can deduce the following:
    # Arnold loves pizza, so he must be in house 2.
    # The person who loves grilled cheese is directly left of the person whose child is named Fred.
    # Therefore, Eric must be in house 1 with Bella, and Arnold must be in house 2 with Fred.
    
    # Construct the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Children", "Food"],
            "rows": [
                ["1", "Eric", "Bella", "grilled cheese"],
                ["2", "Arnold", "Fred", "pizza"]
            ]
        }
    }
    
    # Convert the solution to a JSON string and print it
    return json.dumps(solution, indent=2)

# Run the function and print the result
print(solve_puzzle())