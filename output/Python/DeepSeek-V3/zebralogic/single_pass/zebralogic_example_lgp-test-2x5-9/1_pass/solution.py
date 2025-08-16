import json

def solve_puzzle():
    # Initialize possible values for each attribute
    houses = [1, 2]
    names = ["Arnold", "Eric"]
    book_genres = ["science fiction", "mystery"]
    vacations = ["mountain", "beach"]
    animals = ["cat", "horse"]
    music_genres = ["rock", "pop"]

    # Initialize solution structure
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
            "rows": []
        }
    }

    # Create a list to hold possible assignments for each house
    assignments = []

    # Generate all possible combinations for each house
    from itertools import product

    # We'll process each house separately based on constraints
    house1 = {}
    house2 = {}

    # Apply clue 5: The person who loves mystery books is in the first house.
    house1["BookGenre"] = "mystery"
    house2["BookGenre"] = "science fiction"

    # Apply clue 3: The person who loves rock music is the person who loves mystery books.
    house1["MusicGenre"] = "rock"
    # So house2 must have the other music genre
    house2["MusicGenre"] = "pop"

    # Apply clue 2: The person who loves pop music is the person who loves beach vacations.
    # house2 has pop music, so:
    house2["Vacation"] = "beach"
    # So house1 must have the other vacation
    house1["Vacation"] = "mountain"

    # Apply clue 1: The person who loves beach vacations is Eric.
    # house2 has beach vacation, so:
    house2["Name"] = "Eric"
    # So house1 must have the other name
    house1["Name"] = "Arnold"

    # Apply clue 4: The cat lover is not in the second house.
    # So cat must be in house1, horse in house2
    house1["Animal"] = "cat"
    house2["Animal"] = "horse"

    # Now build the solution rows
    solution["solution"]["rows"].append([
        "1",
        house1["Name"],
        house1["BookGenre"],
        house1["Vacation"],
        house1["Animal"],
        house1["MusicGenre"]
    ])
    solution["solution"]["rows"].append([
        "2",
        house2["Name"],
        house2["BookGenre"],
        house2["Vacation"],
        house2["Animal"],
        house2["MusicGenre"]
    ])

    return json.dumps(solution)

print(solve_puzzle())