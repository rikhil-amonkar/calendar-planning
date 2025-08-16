#!/usr/bin/env python3
import json
import itertools

def main():
    # Define the puzzle parameters
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    book_genres = ["science fiction", "mystery"]
    
    # We'll search over all possible assignments for names and book genres.
    solutions = []
    for name_perm in itertools.permutations(names):
        for genre_perm in itertools.permutations(book_genres):
            # Build a configuration for the two houses with the current permutation
            config = []
            for i, house in enumerate(houses):
                config.append({
                    "House": house,
                    "Name": name_perm[i],
                    "BookGenre": genre_perm[i]
                })
            
            # Apply the constraint: Eric is directly left of the person who loves mystery books.
            # That means for an adjacent pair of houses (i, i+1):
            # If house i has name Eric, then house i+1 must have the book genre mystery.
            valid = False
            for i in range(len(config) - 1):
                if config[i]["Name"] == "Eric" and config[i+1]["BookGenre"] == "mystery":
                    valid = True
                    break
            if not valid:
                continue

            # If valid, add this configuration to the solutions list.
            solutions.append(config)
    
    # Assume there is only one valid solution given the constraints.
    if solutions:
        solution = solutions[0]
    else:
        solution = []
    
    # Prepare the result as required
    result = {
        "solution": {
            "header": ["House", "Name", "BookGenre"],
            "rows": []
        }
    }
    
    # Sort the solution by house number to keep the order (house 1 then house 2).
    solution_sorted = sorted(solution, key=lambda x: x["House"])
    for house in solution_sorted:
        row = [str(house["House"]), house["Name"], house["BookGenre"]]
        result["solution"]["rows"].append(row)
    
    # Output the result as a JSON-formatted string.
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()