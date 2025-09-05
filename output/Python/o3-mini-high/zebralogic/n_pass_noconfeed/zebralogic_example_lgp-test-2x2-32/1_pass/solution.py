import itertools
import json

def main():
    # Define puzzle parameters
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    book_genres = ["science fiction", "mystery"]
    
    # We need to assign each house a unique name and a unique book genre.
    # Clue: Eric is directly left of the person who loves mystery books.
    solution = None
    
    # Generate all possible assignments for names and book genres to houses.
    for name_perm in itertools.permutations(names):
        for genre_perm in itertools.permutations(book_genres):
            # Map each house to its assigned name and book genre.
            assignment = {
                house: {"Name": name_perm[i], "BookGenre": genre_perm[i]}
                for i, house in enumerate(houses)
            }
            
            # Verify the constraint "Eric is directly left of the person who loves mystery books."
            valid = True
            for i, house in enumerate(houses):
                if assignment[house]["Name"] == "Eric":
                    # Eric cannot be in the rightmost house
                    if i == len(houses) - 1:
                        valid = False
                    else:
                        next_house = houses[i + 1]
                        if assignment[next_house]["BookGenre"] != "mystery":
                            valid = False
                    break  # Only need to check where Eric is assigned.
            
            if valid:
                solution = assignment
                break
        if solution is not None:
            break

    # Build the output JSON in the required structure.
    output = {
        "solution": {
            "header": ["House", "Name", "BookGenre"],
            "rows": [
                [str(house), solution[house]["Name"], solution[house]["BookGenre"]]
                for house in houses
            ]
        }
    }
    
    # Print the JSON-formatted output.
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()