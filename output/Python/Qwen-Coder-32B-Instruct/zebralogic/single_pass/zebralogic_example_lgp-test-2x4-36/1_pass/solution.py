import json

def solve_puzzle():
    # Define the possible attributes
    names = ["Eric", "Arnold"]
    books = ["science fiction", "mystery"]
    birthdays = ["april", "sept"]
    animals = ["horse", "cat"]

    # Initialize the houses
    houses = [{}, {}]

    # Apply the clues
    # Clue 1: Eric is in the first house.
    houses[0]["Name"] = "Eric"
    
    # Clue 2: Eric is the person whose birthday is in September.
    houses[0]["Birthday"] = "sept"
    
    # Clue 3: The person who loves science fiction books is in the second house.
    houses[1]["Book"] = "science fiction"
    
    # Clue 4: The person who keeps horses is the person whose birthday is in September.
    houses[0]["Animal"] = "horse"
    
    # Deduce the remaining attributes
    # Since Eric is in the first house, Arnold must be in the second house
    houses[1]["Name"] = [name for name in names if name != houses[0]["Name"]][0]
    
    # Since Eric's birthday is in September, Arnold's birthday must be in April
    houses[1]["Birthday"] = [birthday for birthday in birthdays if birthday != houses[0]["Birthday"]][0]
    
    # Since the person in the second house loves science fiction, they cannot love mystery
    houses[1]["Book"] = "science fiction"
    houses[0]["Book"] = [book for book in books if book != houses[1]["Book"]][0]
    
    # Since Eric keeps horses, Arnold must keep cats
    houses[1]["Animal"] = [animal for animal in animals if animal != houses[0]["Animal"]][0]

    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "Book", "Birthday", "Animal"],
            "rows": [
                ["1", houses[0]["Name"], houses[0]["Book"], houses[0]["Birthday"], houses[0]["Animal"]],
                ["2", houses[1]["Name"], houses[1]["Book"], houses[1]["Birthday"], houses[1]["Animal"]]
            ]
        }
    }

    # Output the solution as JSON
    return json.dumps(solution, indent=2)

# Execute the function and print the result
print(solve_puzzle())