import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each attribute
    names = ["Eric", "Arnold"]
    hobbies = ["gardening", "photography"]
    book_genres = ["science fiction", "mystery"]
    music_genres = ["rock", "pop"]
    birthdays = ["april", "sept"]
    
    houses = [1, 2]
    
    # Generate all possible permutations for each attribute across houses
    # Since there are 2 houses, each permutation is a complete assignment
    solutions = []
    
    # Try all possible assignments
    for name_perm in permutations(names, 2):
        for hobby_perm in permutations(hobbies, 2):
            for book_perm in permutations(book_genres, 2):
                for music_perm in permutations(music_genres, 2):
                    for birthday_perm in permutations(birthdays, 2):
                        # Create assignment dictionary
                        assignment = {}
                        for i, house in enumerate(houses):
                            assignment[house] = {
                                "Name": name_perm[i],
                                "Hobby": hobby_perm[i],
                                "BookGenre": book_perm[i],
                                "MusicGenre": music_perm[i],
                                "Birthday": birthday_perm[i]
                            }
                        
                        # Check all constraints
                        # Clue 1: The person who loves mystery books is the person who loves rock music.
                        clue1_ok = True
                        for house in houses:
                            if assignment[house]["BookGenre"] == "mystery":
                                if assignment[house]["MusicGenre"] != "rock":
                                    clue1_ok = False
                                    break
                            if assignment[house]["MusicGenre"] == "rock":
                                if assignment[house]["BookGenre"] != "mystery":
                                    clue1_ok = False
                                    break
                        if not clue1_ok:
                            continue
                        
                        # Clue 2: Arnold is not in the first house.
                        if assignment[1]["Name"] == "Arnold":
                            continue
                        
                        # Clue 3: The person who loves mystery books is the person who enjoys gardening.
                        clue3_ok = True
                        for house in houses:
                            if assignment[house]["BookGenre"] == "mystery":
                                if assignment[house]["Hobby"] != "gardening":
                                    clue3_ok = False
                                    break
                            if assignment[house]["Hobby"] == "gardening":
                                if assignment[house]["BookGenre"] != "mystery":
                                    clue3_ok = False
                                    break
                        if not clue3_ok:
                            continue
                        
                        # Clue 4: The person whose birthday is in April is Arnold.
                        clue4_ok = True
                        for house in houses:
                            if assignment[house]["Birthday"] == "april":
                                if assignment[house]["Name"] != "Arnold":
                                    clue4_ok = False
                                    break
                            if assignment[house]["Name"] == "Arnold":
                                if assignment[house]["Birthday"] != "april":
                                    clue4_ok = False
                                    break
                        if not clue4_ok:
                            continue
                        
                        # Clue 5: The person who loves mystery books is in the first house.
                        if assignment[1]["BookGenre"] != "mystery":
                            continue
                        
                        # All constraints satisfied
                        solutions.append(assignment)
    
    # We should have exactly one solution
    if len(solutions) != 1:
        raise ValueError(f"Expected exactly 1 solution, found {len(solutions)}")
    
    # Format the solution as required
    solution = solutions[0]
    rows = []
    for house in sorted(solution.keys()):
        row = [
            str(house),
            solution[house]["Name"],
            solution[house]["Hobby"],
            solution[house]["BookGenre"],
            solution[house]["MusicGenre"],
            solution[house]["Birthday"]
        ]
        rows.append(row)
    
    result = {
        "solution": {
            "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
            "rows": rows
        }
    }
    
    return json.dumps(result, indent=2)

if __name__ == "__main__":
    try:
        output = solve_puzzle()
        print(output)
    except Exception as e:
        print(json.dumps({"error": str(e)}, indent=2))