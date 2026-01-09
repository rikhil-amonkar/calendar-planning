import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house (1-4)
    houses = [1, 2, 3, 4]
    
    # Define all possible values for each attribute
    names = ["Peter", "Alice", "Eric", "Arnold"]
    hobbies = ["cooking", "painting", "gardening", "photography"]
    animals = ["horse", "fish", "cat", "bird"]
    book_genres = ["fantasy", "mystery", "romance", "science fiction"]
    birthdays = ["april", "jan", "sept", "feb"]
    music_genres = ["pop", "rock", "classical", "jazz"]
    
    # Add variables for each attribute per house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"hobby_{house}", hobbies)
        problem.addVariable(f"animal_{house}", animals)
        problem.addVariable(f"book_{house}", book_genres)
        problem.addVariable(f"birthday_{house}", birthdays)
        problem.addVariable(f"music_{house}", music_genres)
    
    # All attributes must be different across houses
    for attr in ["name", "hobby", "animal", "book", "birthday", "music"]:
        problem.addConstraint(AllDifferentConstraint(), [f"{attr}_{house}" for house in houses])
    
    # Clue 1: The person who loves cooking is the person who loves romance books.
    for house in houses:
        problem.addConstraint(
            lambda hobby, book: (hobby == "cooking") == (book == "romance"),
            [f"hobby_{house}", f"book_{house}"]
        )
    
    # Clue 2: The person whose birthday is in February is the person who loves pop music.
    for house in houses:
        problem.addConstraint(
            lambda birthday, music: (birthday == "feb") == (music == "pop"),
            [f"birthday_{house}", f"music_{house}"]
        )
    
    # Clue 3: Eric is not in the second house.
    problem.addConstraint(lambda name: name != "Eric", ["name_2"])
    
    # Clue 4: The person who loves romance books is not in the fourth house.
    problem.addConstraint(lambda book: book != "romance", ["book_4"])
    
    # Clue 5: The person whose birthday is in February is the fish enthusiast.
    for house in houses:
        problem.addConstraint(
            lambda birthday, animal: (birthday == "feb") == (animal == "fish"),
            [f"birthday_{house}", f"animal_{house}"]
        )
    
    # Clue 6: Alice is somewhere to the right of the person who loves fantasy books.
    def alice_right_of_fantasy(*args):
        alice_house = None
        fantasy_house = None
        for i, (name, book) in enumerate(args):
            if name == "Alice":
                alice_house = i + 1
            if book == "fantasy":
                fantasy_house = i + 1
        return alice_house is not None and fantasy_house is not None and alice_house > fantasy_house
    
    problem.addConstraint(
        alice_right_of_fantasy,
        [(f"name_{house}", f"book_{house}") for house in houses]
    )
    
    # Clue 7: The person who keeps horses is the person who loves rock music.
    for house in houses:
        problem.addConstraint(
            lambda animal, music: (animal == "horse") == (music == "rock"),
            [f"animal_{house}", f"music_{house}"]
        )
    
    # Clue 8: The person who enjoys gardening is the person whose birthday is in April.
    for house in houses:
        problem.addConstraint(
            lambda hobby, birthday: (hobby == "gardening") == (birthday == "april"),
            [f"hobby_{house}", f"birthday_{house}"]
        )
    
    # Clue 9: The person who loves jazz music is the person who loves cooking.
    for house in houses:
        problem.addConstraint(
            lambda music, hobby: (music == "jazz") == (hobby == "cooking"),
            [f"music_{house}", f"hobby_{house}"]
        )
    
    # Clue 10: The person who loves rock music is the person who loves mystery books.
    for house in houses:
        problem.addConstraint(
            lambda music, book: (music == "rock") == (book == "mystery"),
            [f"music_{house}", f"book_{house}"]
        )
    
    # Clue 11: The person who paints as a hobby is directly left of the person who loves romance books.
    for house in range(1, 4):
        problem.addConstraint(
            lambda hobby, next_book: not (hobby == "painting") or next_book == "romance",
            [f"hobby_{house}", f"book_{house+1}"]
        )
    
    # Clue 12: Peter is the person who loves pop music.
    for house in houses:
        problem.addConstraint(
            lambda name, music: (name == "Peter") == (music == "pop"),
            [f"name_{house}", f"music_{house}"]
        )
    
    # Clue 13: The person who enjoys gardening is Arnold.
    for house in houses:
        problem.addConstraint(
            lambda hobby, name: (hobby == "gardening") == (name == "Arnold"),
            [f"hobby_{house}", f"name_{house}"]
        )
    
    # Clue 14: The person who loves rock music is directly left of the person whose birthday is in January.
    for house in range(1, 4):
        problem.addConstraint(
            lambda music, next_birthday: not (music == "rock") or next_birthday == "jan",
            [f"music_{house}", f"birthday_{house+1}"]
        )
    
    # Clue 15: The person who loves cooking is not in the third house.
    problem.addConstraint(lambda hobby: hobby != "cooking", ["hobby_3"])
    
    # Clue 16: The cat lover is somewhere to the right of the person who keeps horses.
    def cat_right_of_horse(*args):
        cat_house = None
        horse_house = None
        for i, animal in enumerate(args):
            if animal == "cat":
                cat_house = i + 1
            if animal == "horse":
                horse_house = i + 1
        return cat_house is not None and horse_house is not None and cat_house > horse_house
    
    problem.addConstraint(
        cat_right_of_horse,
        [f"animal_{house}" for house in houses]
    )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the result structure
    header = ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"]
    rows = []
    
    for house in houses:
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"hobby_{house}"],
            solution[f"animal_{house}"],
            solution[f"book_{house}"],
            solution[f"birthday_{house}"],
            solution[f"music_{house}"]
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))