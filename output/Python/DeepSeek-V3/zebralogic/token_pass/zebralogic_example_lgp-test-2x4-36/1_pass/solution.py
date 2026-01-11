import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ["Eric", "Arnold"]
    genres = ["science fiction", "mystery"]
    birthdays = ["april", "sept"]
    animals = ["horse", "cat"]
    houses = [1, 2]
    
    # Generate all possible permutations for each house
    # We'll brute-force over all possible assignments
    solutions = []
    
    # Since there are only 2 houses, we can enumerate all possibilities
    for name_perm in permutations(names, 2):
        for genre_perm in permutations(genres, 2):
            for birthday_perm in permutations(birthdays, 2):
                for animal_perm in permutations(animals, 2):
                    # Create assignment for each house
                    assignment = []
                    for i in range(2):
                        assignment.append({
                            "House": str(i + 1),
                            "Name": name_perm[i],
                            "BookGenre": genre_perm[i],
                            "Birthday": birthday_perm[i],
                            "Animal": animal_perm[i]
                        })
                    
                    # Check all clues
                    # Clue 1: Eric is in the first house
                    if assignment[0]["Name"] != "Eric":
                        continue
                    
                    # Clue 2: Eric is the person whose birthday is in September
                    eric_house = 0 if assignment[0]["Name"] == "Eric" else 1
                    if assignment[eric_house]["Birthday"] != "sept":
                        continue
                    
                    # Clue 3: The person who loves science fiction books is in the second house
                    if assignment[1]["BookGenre"] != "science fiction":
                        continue
                    
                    # Clue 4: The person who keeps horses is the person whose birthday is in September
                    # Find the house with horse
                    horse_house = 0 if assignment[0]["Animal"] == "horse" else 1
                    if assignment[horse_house]["Birthday"] != "sept":
                        continue
                    
                    # Also check that the person with birthday in sept has horse
                    sept_house = 0 if assignment[0]["Birthday"] == "sept" else 1
                    if assignment[sept_house]["Animal"] != "horse":
                        continue
                    
                    # All clues satisfied, add to solutions
                    solutions.append(assignment)
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first valid solution
    solution = solutions[0]
    
    # Format the output as required
    header = ["House", "Name", "BookGenre", "Birthday", "Animal"]
    rows = []
    
    for house in sorted(solution, key=lambda x: int(x["House"])):
        rows.append([
            house["House"],
            house["Name"],
            house["BookGenre"],
            house["Birthday"],
            house["Animal"]
        ])
    
    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))