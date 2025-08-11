import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Arnold", "Eric", "Peter", "Alice", "Carol", "Bob"]
    genres = ["jazz", "pop", "classical", "rock", "hip hop", "country"]

    # Generate all possible permutations for names and genres
    for name_perm in permutations(names):
        name_assignment = {house: name for house, name in zip(houses, name_perm)}
        
        # Check Carol is in house 6 (clue 3)
        if name_assignment[6] != "Carol":
            continue
        
        # Check Arnold is not in house 5 (clue 6)
        if name_assignment[5] == "Arnold":
            continue
        
        for genre_perm in permutations(genres):
            genre_assignment = {house: genre for house, genre in zip(houses, genre_perm)}
            
            # Check Carol loves country (clue 5)
            if genre_assignment[6] != "country":
                continue
            
            # Check hip hop is in house 3 (clue 9)
            if genre_assignment[3] != "hip hop":
                continue
            
            # Check Eric is left of hip hop (clue 2) and next to hip hop (clue 4)
            # Since hip hop is in 3, Eric must be in 2
            if name_assignment[2] != "Eric":
                continue
            
            # Check pop is Peter (clue 8)
            pop_house = [h for h in houses if genre_assignment[h] == "pop"][0]
            if name_assignment[pop_house] != "Peter":
                continue
            
            # Check one house between Peter and Bob (clue 10)
            bob_house = [h for h in houses if name_assignment[h] == "Bob"][0]
            if abs(pop_house - bob_house) != 2:
                continue
            
            # Check Bob is directly left of jazz (clue 1)
            jazz_house = bob_house + 1
            if jazz_house > 6 or genre_assignment[jazz_house] != "jazz":
                continue
            
            # Check Arnold is right of pop (clue 7)
            arnold_house = [h for h in houses if name_assignment[h] == "Arnold"][0]
            if arnold_house < pop_house:
                continue
            
            # Check rock is not in house 5 (clue 11)
            if genre_assignment[5] == "rock":
                continue
            
            # All checks passed, construct solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "Music genre"],
                    "rows": []
                }
            }
            for house in houses:
                solution["solution"]["rows"].append([
                    str(house),
                    name_assignment[house],
                    genre_assignment[house]
                ])
            return solution
    
    return {"solution": {}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))