import json

def solve_puzzle():
    # Define the possible values for each characteristic
    names = ["Eric", "Arnold"]
    book_genres = ["science fiction", "mystery"]
    
    # Initialize the possible solutions
    solutions = []
    
    # Generate all possible permutations of names and book genres for two houses
    for name1 in names:
        for genre1 in book_genres:
            for name2 in names:
                if name2 != name1:  # Ensure different people in different houses
                    for genre2 in book_genres:
                        if genre2 != genre1:  # Ensure different book genres in different houses
                            # Check the clue: Eric is directly left of the person who loves mystery books
                            if (name1 == "Eric" and genre2 == "mystery") or (name2 == "Eric" and genre1 == "mystery"):
                                # Add the valid solution to the list
                                solutions.append([["1", name1, genre1], ["2", name2, genre2]])
    
    # Format the solution as JSON
    solution_json = {
        "solution": {
            "header": ["House", "Name", "BookGenre"],
            "rows": solutions[0]  # There should be only one valid solution
        }
    }
    
    # Print the JSON solution
    print(json.dumps(solution_json, indent=2))

# Run the function to solve the puzzle
solve_puzzle()