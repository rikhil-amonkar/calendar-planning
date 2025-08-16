import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Arnold", "Eric", "Peter", "Alice", "Carol", "Bob"]
    genres = ["jazz", "pop", "classical", "rock", "hip hop", "country"]
    
    # Generate all possible permutations for names and genres
    for name_perm in permutations(names):
        for genre_perm in permutations(genres):
            assignment = {house: {"Name": name, "MusicGenre": genre} 
                          for house, name, genre in zip(houses, name_perm, genre_perm)}
            
            # Check constraints
            # Constraint 3: Carol is in the sixth house.
            if assignment[6]["Name"] != "Carol":
                continue
            
            # Constraint 5: The person who loves country music is Carol.
            if assignment[6]["MusicGenre"] != "country":
                continue
            
            # Constraint 9: The person who loves hip-hop music is in the third house.
            if assignment[3]["MusicGenre"] != "hip hop":
                continue
            
            # Constraint 4: Eric and the person who loves hip-hop music are next to each other.
            eric_house = None
            for house in houses:
                if assignment[house]["Name"] == "Eric":
                    eric_house = house
                    break
            if eric_house is None:
                continue
            if abs(eric_house - 3) != 1:
                continue
            
            # Constraint 2: Eric is somewhere to the left of the person who loves hip-hop music.
            if eric_house >= 3:
                continue
            
            # Constraint 8: The person who loves pop music is Peter.
            peter_house = None
            for house in houses:
                if assignment[house]["Name"] == "Peter":
                    peter_house = house
                    break
            if peter_house is None:
                continue
            if assignment[peter_house]["MusicGenre"] != "pop":
                continue
            
            # Constraint 10: There is one house between Peter and Bob.
            bob_house = None
            for house in houses:
                if assignment[house]["Name"] == "Bob":
                    bob_house = house
                    break
            if bob_house is None:
                continue
            if abs(peter_house - bob_house) != 2:
                continue
            
            # Constraint 1: Bob is directly left of the person who loves jazz music.
            jazz_house = bob_house + 1
            if jazz_house > 6 or assignment[jazz_house]["MusicGenre"] != "jazz":
                continue
            
            # Constraint 6: Arnold is not in the fifth house.
            if assignment[5]["Name"] == "Arnold":
                continue
            
            # Constraint 7: Arnold is somewhere to the right of the person who loves pop music.
            arnold_house = None
            for house in houses:
                if assignment[house]["Name"] == "Arnold":
                    arnold_house = house
                    break
            if arnold_house is None:
                continue
            if arnold_house <= peter_house:
                continue
            
            # Constraint 11: The person who loves rock music is not in the fifth house.
            if assignment[5]["MusicGenre"] == "rock":
                continue
            
            # All constraints satisfied, prepare the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "MusicGenre"],
                    "rows": [
                        [str(house), assignment[house]["Name"], assignment[house]["MusicGenre"]] 
                        for house in houses
                    ]
                }
            }
            return json.dumps(solution, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())