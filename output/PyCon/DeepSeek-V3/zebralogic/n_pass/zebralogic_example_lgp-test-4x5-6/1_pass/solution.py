import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house (1-4)
    houses = [1, 2, 3, 4]
    
    # Define domains for each attribute
    names = ["Peter", "Eric", "Alice", "Arnold"]
    educations = ["bachelor", "high school", "associate", "master"]
    music_genres = ["jazz", "rock", "pop", "classical"]
    colors = ["green", "red", "yellow", "white"]
    flowers = ["lilies", "carnations", "daffodils", "roses"]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"education_{house}", educations)
        problem.addVariable(f"music_{house}", music_genres)
        problem.addVariable(f"color_{house}", colors)
        problem.addVariable(f"flower_{house}", flowers)
    
    # All attributes must be different across houses
    for attr in ["name", "education", "music", "color", "flower"]:
        problem.addConstraint(AllDifferentConstraint(), [f"{attr}_{house}" for house in houses])
    
    # Clue 1: The person with a bachelor's degree is the person who loves a bouquet of daffodils.
    for house in houses:
        problem.addConstraint(
            lambda education, flower: not (education == "bachelor") or (flower == "daffodils"),
            [f"education_{house}", f"flower_{house}"]
        )
        problem.addConstraint(
            lambda education, flower: not (flower == "daffodils") or (education == "bachelor"),
            [f"education_{house}", f"flower_{house}"]
        )
    
    # Clue 2: The person who loves a carnations arrangement is not in the first house.
    problem.addConstraint(lambda flower: flower != "carnations", ["flower_1"])
    
    # Clue 3: The person with a master's degree is Alice.
    for house in houses:
        problem.addConstraint(
            lambda education, name: not (education == "master") or (name == "Alice"),
            [f"education_{house}", f"name_{house}"]
        )
        problem.addConstraint(
            lambda education, name: not (name == "Alice") or (education == "master"),
            [f"education_{house}", f"name_{house}"]
        )
    
    # Clue 4: The person with a master's degree is directly left of the person who loves classical music.
    for i in range(1, 4):
        problem.addConstraint(
            lambda edu_left, music_right: not (edu_left == "master") or (music_right == "classical"),
            [f"education_{i}", f"music_{i+1}"]
        )
    
    # Clue 5: Eric is not in the second house.
    problem.addConstraint(lambda name: name != "Eric", ["name_2"])
    
    # Clue 6: Arnold is not in the third house.
    problem.addConstraint(lambda name: name != "Arnold", ["name_3"])
    
    # Clue 7: The person who loves yellow is directly left of the person who loves the rose bouquet.
    for i in range(1, 4):
        problem.addConstraint(
            lambda color_left, flower_right: not (color_left == "yellow") or (flower_right == "roses"),
            [f"color_{i}", f"flower_{i+1}"]
        )
    
    # Clue 8: The person who loves pop music is in the second house.
    problem.addConstraint(lambda music: music == "pop", ["music_2"])
    
    # Clue 9: The person with an associate's degree is not in the fourth house.
    problem.addConstraint(lambda education: education != "associate", ["education_4"])
    
    # Clue 10: The person who loves a carnations arrangement is not in the fourth house.
    problem.addConstraint(lambda flower: flower != "carnations", ["flower_4"])
    
    # Clue 11: The person whose favorite color is red is directly left of the person who loves white.
    for i in range(1, 4):
        problem.addConstraint(
            lambda color_left, color_right: not (color_left == "red") or (color_right == "white"),
            [f"color_{i}", f"color_{i+1}"]
        )
    
    # Clue 12: The person whose favorite color is red is the person who loves rock music.
    for house in houses:
        problem.addConstraint(
            lambda color, music: not (color == "red") or (music == "rock"),
            [f"color_{house}", f"music_{house}"]
        )
        problem.addConstraint(
            lambda color, music: not (music == "rock") or (color == "red"),
            [f"color_{house}", f"music_{house}"]
        )
    
    # Clue 13: Arnold is the person who loves yellow.
    for house in houses:
        problem.addConstraint(
            lambda name, color: not (name == "Arnold") or (color == "yellow"),
            [f"name_{house}", f"color_{house}"]
        )
        problem.addConstraint(
            lambda name, color: not (color == "yellow") or (name == "Arnold"),
            [f"name_{house}", f"color_{house}"]
        )
    
    # Clue 14: The person who loves a bouquet of daffodils is the person who loves yellow.
    for house in houses:
        problem.addConstraint(
            lambda flower, color: not (flower == "daffodils") or (color == "yellow"),
            [f"flower_{house}", f"color_{house}"]
        )
        problem.addConstraint(
            lambda flower, color: not (color == "yellow") or (flower == "daffodils"),
            [f"flower_{house}", f"color_{house}"]
        )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Format the solution
    header = ["House", "Name", "Education", "MusicGenre", "Color", "Flower"]
    rows = []
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"education_{house}"],
            solution[f"music_{house}"],
            solution[f"color_{house}"],
            solution[f"flower_{house}"]
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))