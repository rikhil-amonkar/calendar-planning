import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ["Arnold", "Eric"]
    book_genres = ["science fiction", "mystery"]
    vacations = ["mountain", "beach"]
    animals = ["cat", "horse"]
    music_genres = ["rock", "pop"]
    
    houses = [1, 2]
    
    # Generate all possible permutations for each category across 2 houses
    all_name_perms = list(permutations(names, 2))
    all_book_perms = list(permutations(book_genres, 2))
    all_vacation_perms = list(permutations(vacations, 2))
    all_animal_perms = list(permutations(animals, 2))
    all_music_perms = list(permutations(music_genres, 2))
    
    solutions = []
    
    # Brute force search through all combinations
    for name_perm in all_name_perms:
        for book_perm in all_book_perms:
            for vacation_perm in all_vacation_perms:
                for animal_perm in all_animal_perms:
                    for music_perm in all_music_perms:
                        # Create assignment dictionaries
                        assignment = {}
                        for i, house in enumerate(houses):
                            assignment[house] = {
                                "Name": name_perm[i],
                                "BookGenre": book_perm[i],
                                "Vacation": vacation_perm[i],
                                "Animal": animal_perm[i],
                                "MusicGenre": music_perm[i]
                            }
                        
                        # Check all clues
                        # Clue 1: The person who loves beach vacations is Eric.
                        beach_house = None
                        for house in houses:
                            if assignment[house]["Vacation"] == "beach":
                                beach_house = house
                                break
                        
                        if beach_house is None:
                            continue
                        
                        if assignment[beach_house]["Name"] != "Eric":
                            continue
                        
                        # Clue 2: The person who loves pop music is the person who loves beach vacations.
                        pop_house = None
                        for house in houses:
                            if assignment[house]["MusicGenre"] == "pop":
                                pop_house = house
                                break
                        
                        if pop_house is None or pop_house != beach_house:
                            continue
                        
                        # Clue 3: The person who loves rock music is the person who loves mystery books.
                        rock_house = None
                        mystery_house = None
                        for house in houses:
                            if assignment[house]["MusicGenre"] == "rock":
                                rock_house = house
                            if assignment[house]["BookGenre"] == "mystery":
                                mystery_house = house
                        
                        if rock_house is None or mystery_house is None or rock_house != mystery_house:
                            continue
                        
                        # Clue 4: The cat lover is not in the second house.
                        cat_house = None
                        for house in houses:
                            if assignment[house]["Animal"] == "cat":
                                cat_house = house
                                break
                        
                        if cat_house is None or cat_house == 2:
                            continue
                        
                        # Clue 5: The person who loves mystery books is in the first house.
                        if mystery_house != 1:
                            continue
                        
                        # All clues satisfied, add to solutions
                        solutions.append(assignment)
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first solution (should be only one)
    solution = solutions[0]
    
    # Format the output as required
    header = ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"]
    rows = []
    
    for house in sorted(solution.keys()):
        row = [str(house)]
        row.append(solution[house]["Name"])
        row.append(solution[house]["BookGenre"])
        row.append(solution[house]["Vacation"])
        row.append(solution[house]["Animal"])
        row.append(solution[house]["MusicGenre"])
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))