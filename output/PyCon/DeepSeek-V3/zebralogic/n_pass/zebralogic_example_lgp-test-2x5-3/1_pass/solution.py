import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house
    houses = [1, 2]
    
    # Add variables for each attribute
    for house in houses:
        problem.addVariable(f"name_{house}", ["Eric", "Arnold"])
        problem.addVariable(f"hobby_{house}", ["gardening", "photography"])
        problem.addVariable(f"book_{house}", ["science fiction", "mystery"])
        problem.addVariable(f"music_{house}", ["rock", "pop"])
        problem.addVariable(f"birthday_{house}", ["april", "sept"])
    
    # All attributes must be unique across houses
    for attr in ["name", "hobby", "book", "music", "birthday"]:
        problem.addConstraint(
            lambda *values: len(values) == len(set(values)),
            [f"{attr}_{house}" for house in houses]
        )
    
    # Clue 1: The person who loves mystery books is the person who loves rock music.
    for house in houses:
        problem.addConstraint(
            lambda book, music: not (book == "mystery" and music != "rock") and not (music == "rock" and book != "mystery"),
            [f"book_{house}", f"music_{house}"]
        )
    
    # Clue 2: Arnold is not in the first house.
    problem.addConstraint(lambda name: name != "Arnold", ["name_1"])
    
    # Clue 3: The person who loves mystery books is the person who enjoys gardening.
    for house in houses:
        problem.addConstraint(
            lambda book, hobby: not (book == "mystery" and hobby != "gardening") and not (hobby == "gardening" and book != "mystery"),
            [f"book_{house}", f"hobby_{house}"]
        )
    
    # Clue 4: The person whose birthday is in April is Arnold.
    for house in houses:
        problem.addConstraint(
            lambda birthday, name: not (birthday == "april" and name != "Arnold") and not (name == "Arnold" and birthday != "april"),
            [f"birthday_{house}", f"name_{house}"]
        )
    
    # Clue 5: The person who loves mystery books is in the first house.
    problem.addConstraint(lambda book: book == "mystery", ["book_1"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Build the output structure
    header = ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"]
    rows = []
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"hobby_{house}"],
            solution[f"book_{house}"],
            solution[f"music_{house}"],
            solution[f"birthday_{house}"]
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))