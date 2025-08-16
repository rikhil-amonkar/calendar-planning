import itertools
import json

def solve_puzzle():
    # Define the possible values for each characteristic
    names = ["Eric", "Arnold"]
    book_genres = ["science fiction", "mystery"]
    
    # Generate all possible permutations for the houses
    house_permutations = list(itertools.permutations(names))
    genre_permutations = list(itertools.permutations(book_genres))
    
    # Iterate through all combinations of permutations
    for house_combination in house_permutations:
        for genre_combination in genre_permutations:
            # Unpack the combinations for readability
            name_house1, name_house2 = house_combination
            genre_house1, genre_house2 = genre_combination
            
            # Check the clue: Eric is directly left of the person who loves mystery books.
            if name_house1 == "Eric" and genre_house2 == "mystery":
                # If the condition is satisfied, construct the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "BookGenre"],
                        "rows": [
                            ["1", name_house1, genre_house1],
                            ["2", name_house2, genre_house2]
                        ]
                    }
                }
                # Output the solution as a JSON-formatted string
                print(json.dumps(solution, indent=4))
                return

# Call the function to solve the puzzle
solve_puzzle()