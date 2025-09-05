import itertools
import json

def solve_puzzle():
    houses = [1, 2]
    names = ["Arnold", "Eric"]
    book_genres = ["science fiction", "mystery"]
    vacations = ["mountain", "beach"]
    animals = ["cat", "horse"]
    music_genres = ["rock", "pop"]
    
    # There are 2 houses so we iterate over all permutations (2! for each attribute)
    for perm_names in itertools.permutations(names):
        for perm_books in itertools.permutations(book_genres):
            for perm_vac in itertools.permutations(vacations):
                for perm_anim in itertools.permutations(animals):
                    for perm_music in itertools.permutations(music_genres):
                        # Build candidate solution for each house.
                        sol = []
                        for i in range(2):
                            sol.append({
                                "House": str(houses[i]),
                                "Name": perm_names[i],
                                "BookGenre": perm_books[i],
                                "Vacation": perm_vac[i],
                                "Animal": perm_anim[i],
                                "MusicGenre": perm_music[i]
                            })
                        
                        valid = True
                        
                        # Clue 5: The person who loves mystery books is in the first house.
                        if sol[0]["BookGenre"] != "mystery":
                            valid = False
                        
                        # Clue 3: The person who loves rock music is the person who loves mystery books.
                        for house in sol:
                            # If someone who loves rock doesn't also love mystery books, fail.
                            if house["MusicGenre"] == "rock" and house["BookGenre"] != "mystery":
                                valid = False
                            # If someone who loves mystery books doesn't also love rock music, fail.
                            if house["BookGenre"] == "mystery" and house["MusicGenre"] != "rock":
                                valid = False
                        
                        # Clue 1: The person who loves beach vacations is Eric.
                        for house in sol:
                            if house["Vacation"] == "beach" and house["Name"] != "Eric":
                                valid = False
                        
                        # Clue 2: The person who loves pop music is the person who loves beach vacations.
                        for house in sol:
                            if house["MusicGenre"] == "pop" and house["Vacation"] != "beach":
                                valid = False
                            if house["Vacation"] == "beach" and house["MusicGenre"] != "pop":
                                valid = False
                        
                        # Clue 4: The cat lover is not in the second house.
                        if sol[1]["Animal"] == "cat":
                            valid = False
                        
                        if valid:
                            return sol
    return None

def main():
    solution = solve_puzzle()
    rows = []
    if solution is not None:
        # Ensure houses are output in order (house 1 then house 2)
        for house in solution:
            rows.append([house["House"], house["Name"], house["BookGenre"], house["Vacation"], house["Animal"], house["MusicGenre"]])
    result = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
            "rows": rows
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()