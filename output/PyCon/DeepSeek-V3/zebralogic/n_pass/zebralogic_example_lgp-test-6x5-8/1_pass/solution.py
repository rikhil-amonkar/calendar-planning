import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each attribute
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Arnold", "Peter", "Bob", "Eric", "Carol", "Alice"]
    animals = ["horse", "rabbit", "fish", "cat", "bird", "dog"]
    occupations = ["engineer", "nurse", "lawyer", "teacher", "artist", "doctor"]
    sports = ["basketball", "volleyball", "soccer", "tennis", "baseball", "swimming"]
    heights = ["average", "tall", "short", "very short", "very tall", "super tall"]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"animal_{house}", animals)
        problem.addVariable(f"occupation_{house}", occupations)
        problem.addVariable(f"sport_{house}", sports)
        problem.addVariable(f"height_{house}", heights)
    
    # All attributes must be different
    problem.addConstraint(AllDifferentConstraint(), [f"name_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"animal_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"occupation_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"sport_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"height_{h}" for h in houses])
    
    # Clue 1: The person who is an engineer is the dog owner.
    for house in houses:
        problem.addConstraint(
            lambda occupation, animal: not (occupation == "engineer") or (animal == "dog"),
            [f"occupation_{house}", f"animal_{house}"]
        )
    
    # Clue 2: The person who has an average height is somewhere to the left of the person who is short.
    problem.addConstraint(
        lambda h1, h2, h3, h4, h5, h6: 
            any([h == "average" for h in [h1, h2, h3, h4, h5, h6]]) and 
            any([h == "short" for h in [h1, h2, h3, h4, h5, h6]]) and
            [h1, h2, h3, h4, h5, h6].index("average") < [h1, h2, h3, h4, h5, h6].index("short"),
        [f"height_{h}" for h in houses]
    )
    
    # Clue 3: The person who has an average height is directly left of the rabbit owner.
    for i in range(1, 6):
        problem.addConstraint(
            lambda height_i, animal_i1: not (height_i == "average") or (animal_i1 == "rabbit"),
            [f"height_{i}", f"animal_{i+1}"]
        )
    
    # Clue 4: The person who is tall is somewhere to the left of the person who is very short.
    problem.addConstraint(
        lambda h1, h2, h3, h4, h5, h6: 
            any([h == "tall" for h in [h1, h2, h3, h4, h5, h6]]) and 
            any([h == "very short" for h in [h1, h2, h3, h4, h5, h6]]) and
            [h1, h2, h3, h4, h5, h6].index("tall") < [h1, h2, h3, h4, h5, h6].index("very short"),
        [f"height_{h}" for h in houses]
    )
    
    # Clue 5: Arnold is the cat lover.
    for house in houses:
        problem.addConstraint(
            lambda name, animal: not (name == "Arnold") or (animal == "cat"),
            [f"name_{house}", f"animal_{house}"]
        )
    
    # Clue 6: The person who keeps horses is the person who is a teacher.
    for house in houses:
        problem.addConstraint(
            lambda animal, occupation: not (animal == "horse") or (occupation == "teacher"),
            [f"animal_{house}", f"occupation_{house}"]
        )
    
    # Clue 7: Carol is the person who loves soccer.
    for house in houses:
        problem.addConstraint(
            lambda name, sport: not (name == "Carol") or (sport == "soccer"),
            [f"name_{house}", f"sport_{house}"]
        )
    
    # Clue 8: The person who is tall is the person who loves volleyball.
    for house in houses:
        problem.addConstraint(
            lambda height, sport: not (height == "tall") or (sport == "volleyball"),
            [f"height_{house}", f"sport_{house}"]
        )
    
    # Clue 9: The person who is a lawyer is in the fifth house.
    problem.addConstraint(lambda occupation: occupation == "lawyer", ["occupation_5"])
    
    # Clue 10: The person who loves tennis is the person who is a teacher.
    for house in houses:
        problem.addConstraint(
            lambda sport, occupation: not (sport == "tennis") or (occupation == "teacher"),
            [f"sport_{house}", f"occupation_{house}"]
        )
    
    # Clue 11: The person who has an average height is the person who loves swimming.
    for house in houses:
        problem.addConstraint(
            lambda height, sport: not (height == "average") or (sport == "swimming"),
            [f"height_{house}", f"sport_{house}"]
        )
    
    # Clue 12: The person who loves baseball is directly left of the person who is an engineer.
    for i in range(1, 6):
        problem.addConstraint(
            lambda sport_i, occupation_i1: not (sport_i == "baseball") or (occupation_i1 == "engineer"),
            [f"sport_{i}", f"occupation_{i+1}"]
        )
    
    # Clue 13: Peter is the person who is a nurse.
    for house in houses:
        problem.addConstraint(
            lambda name, occupation: not (name == "Peter") or (occupation == "nurse"),
            [f"name_{house}", f"occupation_{house}"]
        )
    
    # Clue 14: Bob is somewhere to the right of the person who is an artist.
    problem.addConstraint(
        lambda n1, n2, n3, n4, n5, n6, o1, o2, o3, o4, o5, o6: 
            any([n == "Bob" for n in [n1, n2, n3, n4, n5, n6]]) and 
            any([o == "artist" for o in [o1, o2, o3, o4, o5, o6]]) and
            [n1, n2, n3, n4, n5, n6].index("Bob") > [o1, o2, o3, o4, o5, o6].index("artist"),
        [f"name_{h}" for h in houses] + [f"occupation_{h}" for h in houses]
    )
    
    # Clue 15: The person who is a teacher is directly left of the person who loves soccer.
    for i in range(1, 6):
        problem.addConstraint(
            lambda occupation_i, sport_i1: not (occupation_i == "teacher") or (sport_i1 == "soccer"),
            [f"occupation_{i}", f"sport_{i+1}"]
        )
    
    # Clue 16: The rabbit owner is Alice.
    for house in houses:
        problem.addConstraint(
            lambda animal, name: not (animal == "rabbit") or (name == "Alice"),
            [f"animal_{house}", f"name_{house}"]
        )
    
    # Clue 17: The fish enthusiast is Carol.
    for house in houses:
        problem.addConstraint(
            lambda animal, name: not (animal == "fish") or (name == "Carol"),
            [f"animal_{house}", f"name_{house}"]
        )
    
    # Clue 18: The person who loves baseball is in the first house.
    problem.addConstraint(lambda sport: sport == "baseball", ["sport_1"])
    
    # Clue 19: The cat lover is somewhere to the right of the person who is very short.
    problem.addConstraint(
        lambda a1, a2, a3, a4, a5, a6, h1, h2, h3, h4, h5, h6: 
            any([a == "cat" for a in [a1, a2, a3, a4, a5, a6]]) and 
            any([h == "very short" for h in [h1, h2, h3, h4, h5, h6]]) and
            [a1, a2, a3, a4, a5, a6].index("cat") > [h1, h2, h3, h4, h5, h6].index("very short"),
        [f"animal_{h}" for h in houses] + [f"height_{h}" for h in houses]
    )
    
    # Clue 20: The person who is super tall is in the fifth house.
    problem.addConstraint(lambda height: height == "super tall", ["height_5"])
    
    # Solve the puzzle
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Format the solution
    header = ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"]
    rows = []
    
    for house in houses:
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"animal_{house}"],
            solution[f"occupation_{house}"],
            solution[f"sport_{house}"],
            solution[f"height_{house}"]
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))