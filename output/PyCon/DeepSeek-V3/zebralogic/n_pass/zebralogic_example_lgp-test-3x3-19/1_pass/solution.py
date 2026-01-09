import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    # Define variables: house numbers 1, 2, 3
    houses = [1, 2, 3]
    
    # Define domains for each attribute
    names = ["Eric", "Arnold", "Peter"]
    smoothies = ["desert", "watermelon", "cherry"]
    genres = ["science fiction", "romance", "mystery"]
    
    # Add variables for each attribute
    problem.addVariable("name", names)
    problem.addVariable("smoothie", smoothies)
    problem.addVariable("genre", genres)
    
    # All attributes must be different
    problem.addConstraint(lambda n, s, g: len(set([n, s, g])) == 3, 
                         ("name", "smoothie", "genre"))
    
    # Clue 5: Peter is in the first house
    problem.addConstraint(lambda name: name == "Peter", ["name"])
    
    # Clue 2: Arnold is the person who loves mystery books
    problem.addConstraint(lambda name, genre: not (name == "Arnold") or (genre == "mystery"), 
                         ("name", "genre"))
    problem.addConstraint(lambda name, genre: not (genre == "mystery") or (name == "Arnold"), 
                         ("name", "genre"))
    
    # Clue 3: The person who loves science fiction books is not in the first house
    problem.addConstraint(lambda genre: genre != "science fiction", ["genre"])
    
    # Since we're only solving for house 1, we need to approach this differently
    # We'll solve for all houses simultaneously
    
    # Reset the problem to handle all 3 houses
    problem = Problem()
    
    # Add variables for each house and each attribute
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"smoothie_{house}", smoothies)
        problem.addVariable(f"genre_{house}", genres)
    
    # All names must be different across houses
    problem.addConstraint(lambda n1, n2, n3: len(set([n1, n2, n3])) == 3, 
                         [f"name_{house}" for house in houses])
    
    # All smoothies must be different across houses
    problem.addConstraint(lambda s1, s2, s3: len(set([s1, s2, s3])) == 3, 
                         [f"smoothie_{house}" for house in houses])
    
    # All genres must be different across houses
    problem.addConstraint(lambda g1, g2, g3: len(set([g1, g2, g3])) == 3, 
                         [f"genre_{house}" for house in houses])
    
    # Clue 5: Peter is in the first house
    problem.addConstraint(lambda name: name == "Peter", ["name_1"])
    
    # Clue 2: Arnold is the person who loves mystery books
    # Find which house has Arnold and ensure it has mystery genre
    for house in houses:
        problem.addConstraint(lambda name, genre, h=house: not (name == "Arnold") or (genre == "mystery"), 
                             [f"name_{h}", f"genre_{h}"])
        problem.addConstraint(lambda name, genre, h=house: not (genre == "mystery") or (name == "Arnold"), 
                             [f"name_{h}", f"genre_{h}"])
    
    # Clue 3: The person who loves science fiction books is not in the first house
    problem.addConstraint(lambda genre: genre != "science fiction", ["genre_1"])
    
    # Clue 1: The person who likes Cherry smoothies is somewhere to the left of the person who loves mystery books
    def cherry_left_of_mystery(s1, s2, s3, g1, g2, g3):
        cherry_house = None
        mystery_house = None
        
        if s1 == "cherry": cherry_house = 1
        elif s2 == "cherry": cherry_house = 2
        elif s3 == "cherry": cherry_house = 3
        
        if g1 == "mystery": mystery_house = 1
        elif g2 == "mystery": mystery_house = 2
        elif g3 == "mystery": mystery_house = 3
        
        if cherry_house is not None and mystery_house is not None:
            return cherry_house < mystery_house
        return True
    
    problem.addConstraint(cherry_left_of_mystery, 
                         [f"smoothie_{house}" for house in houses] + 
                         [f"genre_{house}" for house in houses])
    
    # Clue 4: The Desert smoothie lover is directly left of the person who loves mystery books
    def desert_left_of_mystery(s1, s2, s3, g1, g2, g3):
        desert_house = None
        mystery_house = None
        
        if s1 == "desert": desert_house = 1
        elif s2 == "desert": desert_house = 2
        elif s3 == "desert": desert_house = 3
        
        if g1 == "mystery": mystery_house = 1
        elif g2 == "mystery": mystery_house = 2
        elif g3 == "mystery": mystery_house = 3
        
        if desert_house is not None and mystery_house is not None:
            return desert_house + 1 == mystery_house
        return True
    
    problem.addConstraint(desert_left_of_mystery, 
                         [f"smoothie_{house}" for house in houses] + 
                         [f"genre_{house}" for house in houses])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Smoothie", "BookGenre"], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the result
    rows = []
    for house in houses:
        name = solution[f"name_{house}"]
        smoothie = solution[f"smoothie_{house}"]
        genre = solution[f"genre_{house}"]
        rows.append([str(house), name, smoothie, genre])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "BookGenre"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))