import json

# Define the possible values for each attribute
names = ["Eric", "Arnold"]
hobbies = ["gardening", "photography"]
book_genres = ["science fiction", "mystery"]
music_genres = ["rock", "pop"]
birthdays = ["april", "sept"]

# Initialize the houses with empty dictionaries
houses = [{}, {}]

# Apply the constraints step by step
# Clue 2: Arnold is not in the first house.
houses[1]["Name"] = "Arnold"

# Clue 4: The person whose birthday is in April is Arnold.
houses[1]["Birthday"] = "april"

# Clue 5: The person who loves mystery books is in the first house.
houses[0]["BookGenre"] = "mystery"

# Clue 1: The person who loves mystery books is the person who loves rock music.
houses[0]["MusicGenre"] = "rock"

# Clue 3: The person who loves mystery books is the person who enjoys gardening.
houses[0]["Hobby"] = "gardening"

# Since Arnold is in the second house, Eric must be in the first house
houses[0]["Name"] = "Eric"

# By elimination, Arnold must enjoy photography and have his birthday in April (already set)
houses[1]["Hobby"] = "photography"
houses[1]["BookGenre"] = "science fiction"
houses[1]["MusicGenre"] = "pop"
houses[1]["Birthday"] = "april"  # already set

# Prepare the solution in the required JSON format
solution = {
    "solution": {
        "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
        "rows": [
            ["1", houses[0]["Name"], houses[0]["Hobby"], houses[0]["BookGenre"], houses[0]["MusicGenre"], houses[0]["Birthday"]],
            ["2", houses[1]["Name"], houses[1]["Hobby"], houses[1]["BookGenre"], houses[1]["MusicGenre"], houses[1]["Birthday"]]
        ]
    }
}

# Convert the solution to JSON and print it
print(json.dumps(solution, indent=2))