import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Eric", "Arnold"]
    hobbies = ["gardening", "photography"]
    book_genres = ["science fiction", "mystery"]
    music_genres = ["rock", "pop"]
    birthday_months = ["april", "sept"]

    # Generate all possible combinations of attributes for two houses
    all_combinations = list(itertools.product(
        names, hobbies, book_genres, music_genres, birthday_months
    ))

    # Function to check if a combination satisfies all the clues
    def is_valid(combination):
        house1, house2 = combination[:5], combination[5:]
        
        # Unpack attributes for each house
        name1, hobby1, book_genre1, music_genre1, birthday_month1 = house1
        name2, hobby2, book_genre2, music_genre2, birthday_month2 = house2
        
        # Check clue 1
        if book_genre1 == "mystery" and (music_genre1 != "rock" or book_genre2 == "mystery"):
            return False
        if book_genre2 == "mystery" and music_genre2 != "rock":
            return False
        
        # Check clue 2
        if name1 == "Arnold":
            return False
        
        # Check clue 3
        if book_genre1 != "mystery" or hobby1 != "gardening":
            return False
        
        # Check clue 4
        if name1 != "Arnold" or birthday_month1 != "april":
            return False
        
        # Check clue 5
        if book_genre1 != "mystery" or name2 == "Arnold":
            return False
        
        return True

    # Find the valid combination
    for combination in itertools.permutations(all_combinations, 2):
        if is_valid(combination):
            house1, house2 = combination
            break

    # Prepare the solution in JSON format
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Favorite Book Genre", "Favorite Music Genre", "Birthday Month"],
            "rows": [
                ["1"] + list(house1),
                ["2"] + list(house2)
            ]
        }
    }

    # Output the solution as JSON
    print(json.dumps(solution, indent=2))

# Run the function to solve the puzzle
solve_puzzle()