import json

def solve_puzzle():
    # Define possible values
    names = ["Eric", "Arnold"]
    book_genres = ["science fiction", "mystery"]
    birthdays = ["april", "sept"]
    animals = ["horse", "cat"]

    # Initialize possible states for each house
    house1 = []
    house2 = []

    # Generate all possible combinations for each house
    for name in names:
        for book_genre in book_genres:
            for birthday in birthdays:
                for animal in animals:
                    house1.append((name, book_genre, birthday, animal))
                    house2.append((name, book_genre, birthday, animal))

    # Apply constraints
    # Constraint 1: Eric is in the first house.
    house1 = [state for state in house1 if state[0] == "Eric"]
    house2 = [state for state in house2 if state[0] != "Eric"]

    # Constraint 2: Eric's birthday is in September.
    house1 = [state for state in house1 if state[2] == "sept"]

    # Constraint 3: The person who loves science fiction books is in the second house.
    house2 = [state for state in house2 if state[1] == "science fiction"]

    # Constraint 4: The person who keeps horses is the person whose birthday is in September.
    house1 = [state for state in house1 if state[3] == "horse"]

    # Now we should have a unique solution for each house
    assert len(house1) == 1 and len(house2) == 1, "No unique solution found"

    # Extract the solutions
    solution_house1 = house1[0]
    solution_house2 = house2[0]

    # Construct the JSON solution
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
            "rows": [
                ["1", solution_house1[0], solution_house1[1], solution_house1[2], solution_house1[3]],
                ["2", solution_house2[0], solution_house2[1], solution_house2[2], solution_house2[3]]
            ]
        }
    }

    return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())