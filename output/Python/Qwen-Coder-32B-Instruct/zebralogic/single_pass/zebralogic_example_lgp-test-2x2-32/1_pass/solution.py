import json

def solve_puzzle():
    # Define the possible attributes
    names = ["Eric", "Arnold"]
    book_genres = ["science fiction", "mystery"]
    
    # Initialize the possible solutions
    possible_solutions = []
    
    # Generate all permutations of names and book genres
    for i in range(2):
        for j in range(2):
            if i != j:  # Ensure each person has a unique name
                for k in range(2):
                    for l in range(2):
                        if k != l:  # Ensure each person has a unique book genre
                            # Create a solution based on the current permutation
                            solution = {
                                "1": {"Name": names[i], "Book Genre": book_genres[k]},
                                "2": {"Name": names[j], "Book Genre": book_genres[l]}
                            }
                            # Check the clue: Eric is directly left of the person who loves mystery books
                            if solution["1"]["Name"] == "Eric" and solution["2"]["Book Genre"] == "mystery":
                                possible_solutions.append(solution)
    
    # Format the solution as required
    formatted_solution = {
        "solution": {
            "header": ["House", "Name", "Book Genre"],
            "rows": [
                ["1", possible_solutions[0]["1"]["Name"], possible_solutions[0]["1"]["Book Genre"]],
                ["2", possible_solutions[0]["2"]["Name"], possible_solutions[0]["2"]["Book Genre"]]
            ]
        }
    }
    
    # Output the solution as JSON
    print(json.dumps(formatted_solution, indent=2))

# Run the function to solve the puzzle
solve_puzzle()