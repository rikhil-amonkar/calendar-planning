import json

def main():
    # Define the attributes
    names = ["Arnold", "Eric"]
    book_genres = ["science fiction", "mystery"]
    vacations = ["mountain", "beach"]
    animals = ["cat", "horse"]
    music_genres = ["rock", "pop"]
    
    # Initialize possibilities for each house
    houses = [1, 2]
    
    # Create all possible assignments for each attribute
    from itertools import permutations
    name_perms = list(permutations(names))
    book_perms = list(permutations(book_genres))
    vacation_perms = list(permutations(vacations))
    animal_perms = list(permutations(animals))
    music_perms = list(permutations(music_genres))
    
    # Try all combinations
    for name_assignment in name_perms:
        for book_assignment in book_perms:
            for vacation_assignment in vacation_perms:
                for animal_assignment in animal_perms:
                    for music_assignment in music_perms:
                        # Create the assignment for house 1 and 2
                        assignment = {
                            1: {
                                "Name": name_assignment[0],
                                "BookGenre": book_assignment[0],
                                "Vacation": vacation_assignment[0],
                                "Animal": animal_assignment[0],
                                "MusicGenre": music_assignment[0]
                            },
                            2: {
                                "Name": name_assignment[1],
                                "BookGenre": book_assignment[1],
                                "Vacation": vacation_assignment[1],
                                "Animal": animal_assignment[1],
                                "MusicGenre": music_assignment[1]
                            }
                        }
                        
                        # Check all constraints
                        # Clue 1: The person who loves beach vacations is Eric.
                        beach_vacation_house = None
                        for house in houses:
                            if assignment[house]["Vacation"] == "beach":
                                beach_vacation_house = house
                                break
                        if assignment[beach_vacation_house]["Name"] != "Eric":
                            continue
                            
                        # Clue 2: The person who loves pop music is the person who loves beach vacations.
                        pop_music_house = None
                        for house in houses:
                            if assignment[house]["MusicGenre"] == "pop":
                                pop_music_house = house
                                break
                        if pop_music_house != beach_vacation_house:
                            continue
                            
                        # Clue 3: The person who loves rock music is the person who loves mystery books.
                        rock_music_house = None
                        mystery_book_house = None
                        for house in houses:
                            if assignment[house]["MusicGenre"] == "rock":
                                rock_music_house = house
                            if assignment[house]["BookGenre"] == "mystery":
                                mystery_book_house = house
                        if rock_music_house != mystery_book_house:
                            continue
                            
                        # Clue 4: The cat lover is not in the second house.
                        cat_house = None
                        for house in houses:
                            if assignment[house]["Animal"] == "cat":
                                cat_house = house
                                break
                        if cat_house == 2:
                            continue
                            
                        # Clue 5: The person who loves mystery books is in the first house.
                        if mystery_book_house != 1:
                            continue
                            
                        # If we reach here, all constraints are satisfied
                        # Format the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
                                "rows": [
                                    ["1", 
                                     assignment[1]["Name"],
                                     assignment[1]["BookGenre"],
                                     assignment[1]["Vacation"],
                                     assignment[1]["Animal"],
                                     assignment[1]["MusicGenre"]],
                                    ["2",
                                     assignment[2]["Name"],
                                     assignment[2]["BookGenre"],
                                     assignment[2]["Vacation"],
                                     assignment[2]["Animal"],
                                     assignment[2]["MusicGenre"]]
                                ]
                            }
                        }
                        
                        # Output the solution as JSON
                        print(json.dumps(solution, indent=2))
                        return
    
    # If no solution found
    print(json.dumps({"solution": {"header": [], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()