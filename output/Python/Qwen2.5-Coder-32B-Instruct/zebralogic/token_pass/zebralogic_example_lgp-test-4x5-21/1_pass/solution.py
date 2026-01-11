import itertools
import json

def apply_clues(grid):
    # Unpack grid into lists for easier manipulation
    names, smoothies, sports, cars, flowers = [list(row) for row in zip(*grid)]
    
    # Clue 1: Tesla Model 3 -> Roses
    tesla_index = cars.index("tesla model 3")
    flowers[tesla_index] = "roses"
    
    # Clue 2: Peter -> Dragonfruit
    peter_index = names.index("peter")
    smoothies[peter_index] = "dragonfruit"
    
    # Clue 3: Desert -> Toyota Camry
    desert_index = smoothies.index("desert")
    cars[desert_index] = "toyota camry"
    
    # Clue 4: Tennis -> House 1
    sports[0] = "tennis"
    
    # Clue 6: Arnold -> Basketball
    arnold_index = names.index("arnold")
    sports[arnold_index] = "basketball"
    
    # Clue 7: Honda Civic -> Daffodils
    honda_index = cars.index("honda civic")
    flowers[honda_index] = "daffodils"
    
    # Clue 8: Eric -> Roses
    eric_index = names.index("eric")
    flowers[eric_index] = "roses"
    
    # Clue 9: Watermelon not in House 1
    if smoothies[0] == "watermelon":
        raise ValueError("Clue 9 conflict")
    
    # Clue 11: Basketball -> Lilies
    basketball_index = sports.index("basketball")
    flowers[basketball_index] = "lilies"
    
    # Clue 5: Toyota Camry & Basketball are neighbors
    toyota_index = cars.index("toyota camry")
    if abs(toyota_index - basketball_index) != 1:
        raise ValueError("Clue 5 conflict")
    
    # Clue 10: Honda Civic is right of Desert
    if honda_index < desert_index:
        raise ValueError("Clue 10 conflict")
    
    # Clue 12: Tennis & Soccer are neighbors
    tennis_index = sports.index("tennis")
    if "soccer" not in sports:
        raise ValueError("Soccer not assigned yet")
    soccer_index = sports.index("soccer")
    if abs(tennis_index - soccer_index) != 1:
        raise ValueError("Clue 12 conflict")
    
    # Ensure all values are unique in each column
    for col in [names, smoothies, sports, cars, flowers]:
        if len(set(col)) != 4:
            raise ValueError("Duplicate values found in a column")
    
    # Update grid with solved values
    for i in range(4):
        grid[i] = (names[i], smoothies[i], sports[i], cars[i], flowers[i])
    return grid

def solve_puzzle():
    # Generate all permutations for initial grid setup
    people = ["eric", "alice", "peter", "arnold"]
    smoothies = ["dragonfruit", "cherry", "desert", "watermelon"]
    sports = ["soccer", "tennis", "basketball", "swimming"]
    cars = ["tesla model 3", "toyota camry", "honda civic", "ford f150"]
    flowers = ["daffodils", "roses", "lilies", "carnations"]
    
    for perm in itertools.permutations(zip(people, smoothies, sports, cars, flowers)):
        try:
            solved_grid = apply_clues(list(perm))
            break
        except ValueError:
            continue
    else:
        raise Exception("No solution found")
    
    # Format the solution as JSON
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
            "rows": [[str(i+1)] + list(row) for i, row in enumerate(solved_grid)]
        }
    }
    return json.dumps(solution, indent=2)

# Run the solver and print the result
print(solve_puzzle())