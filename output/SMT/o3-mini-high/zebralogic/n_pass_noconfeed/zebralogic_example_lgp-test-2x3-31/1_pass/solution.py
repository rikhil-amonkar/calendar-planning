import json
from z3 import *

def main():
    solver = Solver()

    # There are 2 houses. For each house, create Z3 integer variables for Name, FavoriteSport, and Hobby.
    # Domain mapping:
    # Name: 0 -> "Eric", 1 -> "Arnold"
    # FavoriteSport: 0 -> "basketball", 1 -> "soccer"
    # Hobby: 0 -> "photography", 1 -> "gardening"
    houses = 2
    names = [Int(f"name_{i}") for i in range(1, houses+1)]
    sports = [Int(f"sport_{i}") for i in range(1, houses+1)]
    hobbies = [Int(f"hobby_{i}") for i in range(1, houses+1)]

    # Each variable must be either 0 or 1
    for var in names + sports + hobbies:
        solver.add(Or(var == 0, var == 1))

    # Each attribute must be unique across houses
    solver.add(Distinct(names))
    solver.add(Distinct(sports))
    solver.add(Distinct(hobbies))

    # Clue 1: The person who enjoys gardening is Arnold.
    # Gardening has value 1 for Hobby and Arnold has value 1 for Name.
    for i in range(houses):
        solver.add(Implies(hobbies[i] == 1, names[i] == 1))
        solver.add(Implies(names[i] == 1, hobbies[i] == 1))
    
    # Clue 2: The photography enthusiast is not in the first house.
    # Photography has value 0 for Hobby.
    solver.add(hobbies[0] != 0)
    
    # Clue 3: The person who loves soccer is not in the first house.
    # Soccer has value 1 for FavoriteSport.
    solver.add(sports[0] != 1)

    if solver.check() == sat:
        model = solver.model()
        # Mapping from integer values to their corresponding string representation.
        name_map = {0: "Eric", 1: "Arnold"}
        sport_map = {0: "basketball", 1: "soccer"}
        hobby_map = {0: "photography", 1: "gardening"}
        
        rows = []
        for i in range(houses):
            house_number = str(i + 1)
            name_str = name_map[model[names[i]].as_long()]
            sport_str = sport_map[model[sports[i]].as_long()]
            hobby_str = hobby_map[model[hobbies[i]].as_long()]
            rows.append([house_number, name_str, sport_str, hobby_str])
        
        result = {
            "solution": {
                "header": ["House", "Name", "FavoriteSport", "Hobby"],
                "rows": rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()