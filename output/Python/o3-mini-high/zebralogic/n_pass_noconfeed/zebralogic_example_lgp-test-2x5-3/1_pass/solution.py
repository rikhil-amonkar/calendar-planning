import itertools
import json

def solve_puzzle():
    # Define possible values for each attribute
    houses = ["1", "2"]
    names = ["Eric", "Arnold"]
    hobbies = ["gardening", "photography"]
    book_genres = ["science fiction", "mystery"]
    music_genres = ["rock", "pop"]
    birthdays = ["april", "sept"]
    
    solution = None
    
    # Iterate over all possible combinations using permutations
    for perm_names in itertools.permutations(names):
        for perm_hobbies in itertools.permutations(hobbies):
            for perm_books in itertools.permutations(book_genres):
                for perm_music in itertools.permutations(music_genres):
                    for perm_birthdays in itertools.permutations(birthdays):
                        # Create house assignments for house 1 and house 2
                        house1 = {
                            "House": "1",
                            "Name": perm_names[0],
                            "Hobby": perm_hobbies[0],
                            "BookGenre": perm_books[0],
                            "MusicGenre": perm_music[0],
                            "Birthday": perm_birthdays[0]
                        }
                        house2 = {
                            "House": "2",
                            "Name": perm_names[1],
                            "Hobby": perm_hobbies[1],
                            "BookGenre": perm_books[1],
                            "MusicGenre": perm_music[1],
                            "Birthday": perm_birthdays[1]
                        }
                        houses_assignment = [house1, house2]
                        
                        # Constraint 5: The person who loves mystery books is in the first house.
                        if house1["BookGenre"] != "mystery":
                            continue
                            
                        # Constraint 1: The person who loves mystery books is the person who loves rock music.
                        # Constraint 3: The person who loves mystery books is the person who enjoys gardening.
                        if house1["MusicGenre"] != "rock" or house1["Hobby"] != "gardening":
                            continue
                        
                        # Constraint 2: Arnold is not in the first house.
                        if house1["Name"] == "Arnold":
                            continue
                        
                        # Constraint 4: The person whose birthday is in April is Arnold.
                        valid = True
                        for house in houses_assignment:
                            if house["Birthday"] == "april" and house["Name"] != "Arnold":
                                valid = False
                                break
                            if house["Name"] == "Arnold" and house["Birthday"] != "april":
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # If all constraints are satisfied, record the solution
                        solution = houses_assignment
                        break
                    if solution is not None:
                        break
                if solution is not None:
                    break
            if solution is not None:
                break
        if solution is not None:
            break
    return solution

def main():
    solution = solve_puzzle()
    if solution is None:
        result = {
            "solution": {
                "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
                "rows": []
            }
        }
    else:
        # Ensure the houses are ordered by House number
        solution_sorted = sorted(solution, key=lambda x: int(x["House"]))
        rows = []
        for house in solution_sorted:
            rows.append([
                house["House"],
                house["Name"],
                house["Hobby"],
                house["BookGenre"],
                house["MusicGenre"],
                house["Birthday"]
            ])
        result = {
            "solution": {
                "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
                "rows": rows
            }
        }
    print(json.dumps(result))

if __name__ == "__main__":
    main()