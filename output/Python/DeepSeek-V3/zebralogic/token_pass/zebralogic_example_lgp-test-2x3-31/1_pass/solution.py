import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ["Eric", "Arnold"]
    sports = ["basketball", "soccer"]
    hobbies = ["photography", "gardening"]
    houses = ["1", "2"]
    
    # Generate all possible permutations for each category across 2 houses
    name_perms = list(permutations(names, 2))
    sport_perms = list(permutations(sports, 2))
    hobby_perms = list(permutations(hobbies, 2))
    
    solutions = []
    
    # Try all combinations of permutations
    for name_assignment in name_perms:
        for sport_assignment in sport_perms:
            for hobby_assignment in hobby_perms:
                # Build the assignment for each house
                assignment = []
                valid = True
                
                for i in range(2):
                    house_num = str(i + 1)
                    name = name_assignment[i]
                    sport = sport_assignment[i]
                    hobby = hobby_assignment[i]
                    assignment.append([house_num, name, sport, hobby])
                
                # Check clue 1: The person who enjoys gardening is Arnold
                gardening_found = False
                for house in assignment:
                    if house[3] == "gardening" and house[1] == "Arnold":
                        gardening_found = True
                        break
                if not gardening_found:
                    valid = False
                
                # Check clue 2: The photography enthusiast is not in the first house
                for house in assignment:
                    if house[0] == "1" and house[3] == "photography":
                        valid = False
                        break
                
                # Check clue 3: The person who loves soccer is not in the first house
                for house in assignment:
                    if house[0] == "1" and house[2] == "soccer":
                        valid = False
                        break
                
                # Check that all values are unique across houses (should be by construction)
                # But verify no duplicate names, sports, or hobbies
                names_seen = set()
                sports_seen = set()
                hobbies_seen = set()
                
                for house in assignment:
                    if house[1] in names_seen:
                        valid = False
                    if house[2] in sports_seen:
                        valid = False
                    if house[3] in hobbies_seen:
                        valid = False
                    
                    names_seen.add(house[1])
                    sports_seen.add(house[2])
                    hobbies_seen.add(house[3])
                
                if valid:
                    solutions.append(assignment)
    
    # We should have exactly one solution
    if len(solutions) == 1:
        result = {
            "solution": {
                "header": ["House", "Name", "FavoriteSport", "Hobby"],
                "rows": solutions[0]
            }
        }
        return result
    else:
        # Fallback if multiple solutions found (shouldn't happen)
        return {"error": "Multiple solutions found"}

def main():
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    main()