#!/usr/bin/env python3
import itertools
import json

def main():
    # Define the houses and attributes as given in the puzzle
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    book_genres = ["science fiction", "mystery"]
    birthday_months = ["april", "sept"]
    animals = ["horse", "cat"]
    
    # We will search for the valid assignment using permutations and applying constraints.
    solution = None
    
    # Generate all permutations for names, book genres, birthday months, and animals.
    # House numbers are in order: index 0 -> House 1, index 1 -> House 2.
    for perm_names in itertools.permutations(names):
        # Constraint 1: Eric is in the first house.
        if perm_names[0] != "Eric":
            continue
            
        for perm_genres in itertools.permutations(book_genres):
            # Constraint 3: The person who loves science fiction books is in the second house.
            if perm_genres[1] != "science fiction":
                continue
                
            for perm_months in itertools.permutations(birthday_months):
                # Constraint 2: Eric is the person whose birthday is in September.
                if perm_months[0] != "sept":
                    continue
                    
                for perm_animals in itertools.permutations(animals):
                    valid = True
                    # Constraint 4: The person who keeps horses is the person whose birthday is in September.
                    # That is, for each house, if birthday month is sept, then animal must be horse.
                    for i in range(2):
                        if perm_months[i] == "sept" and perm_animals[i] != "horse":
                            valid = False
                            break
                    if not valid:
                        continue
                        
                    # If we have reached here, all constraints have been satisfied.
                    solution = [
                        [ "1", perm_names[0], perm_genres[0], perm_months[0], perm_animals[0] ],
                        [ "2", perm_names[1], perm_genres[1], perm_months[1], perm_animals[1] ]
                    ]
                    break
                if solution is not None:
                    break
            if solution is not None:
                break
        if solution is not None:
            break

    result = {
        "solution": {
            "header": ["House", "Name", "favorite book genres", "birthday month", "animals"],
            "rows": solution
        }
    }
    
    # Output the result as JSON
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()