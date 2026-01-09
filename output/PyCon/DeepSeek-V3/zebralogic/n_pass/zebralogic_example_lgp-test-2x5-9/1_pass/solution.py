from constraint import Problem
import json

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2]
    
    # Define variables for each attribute
    names = ["Arnold", "Eric"]
    book_genres = ["science fiction", "mystery"]
    vacations = ["mountain", "beach"]
    animals = ["cat", "horse"]
    music_genres = ["rock", "pop"]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"book_{house}", book_genres)
        problem.addVariable(f"vacation_{house}", vacations)
        problem.addVariable(f"animal_{house}", animals)
        problem.addVariable(f"music_{house}", music_genres)
    
    # All attributes must be unique across houses
    for attr in ["name", "book", "vacation", "animal", "music"]:
        problem.addConstraint(
            lambda *values: len(values) == len(set(values)),
            [f"{attr}_{house}" for house in houses]
        )
    
    # Clue 1: The person who loves beach vacations is Eric.
    for house in houses:
        problem.addConstraint(
            lambda vacation, name: not (vacation == "beach") or (name == "Eric"),
            [f"vacation_{house}", f"name_{house}"]
        )
    
    # Clue 2: The person who loves pop music is the person who loves beach vacations.
    for house in houses:
        problem.addConstraint(
            lambda music, vacation: not (music == "pop") or (vacation == "beach"),
            [f"music_{house}", f"vacation_{house}"]
        )
    for house in houses:
        problem.addConstraint(
            lambda vacation, music: not (vacation == "beach") or (music == "pop"),
            [f"vacation_{house}", f"music_{house}"]
        )
    
    # Clue 3: The person who loves rock music is the person who loves mystery books.
    for house in houses:
        problem.addConstraint(
            lambda music, book: not (music == "rock") or (book == "mystery"),
            [f"music_{house}", f"book_{house}"]
        )
    for house in houses:
        problem.addConstraint(
            lambda book, music: not (book == "mystery") or (music == "rock"),
            [f"book_{house}", f"music_{house}"]
        )
    
    # Clue 4: The cat lover is not in the second house.
    problem.addConstraint(
        lambda animal_2: animal_2 != "cat",
        [f"animal_2"]
    )
    
    # Clue 5: The person who loves mystery books is in the first house.
    problem.addConstraint(
        lambda book_1: book_1 == "mystery",
        [f"book_1"]
    )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result
    header = ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"]
    rows = []
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"book_{house}"],
            solution[f"vacation_{house}"],
            solution[f"animal_{house}"],
            solution[f"music_{house}"]
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))