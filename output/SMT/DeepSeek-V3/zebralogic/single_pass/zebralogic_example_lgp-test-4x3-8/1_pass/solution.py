from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    s = Solver()

    # Define the houses
    houses = [1, 2, 3, 4]

    # Define the attributes
    names = ["Eric", "Arnold", "Peter", "Alice"]
    hair_colors = ["blonde", "black", "brown", "red"]
    music_genres = ["pop", "jazz", "rock", "classical"]

    # Create variables for each attribute in each house
    name_vars = {house: String(f"name_{house}") for house in houses}
    hair_vars = {house: String(f"hair_{house}") for house in houses}
    music_vars = {house: String(f"music_{house}") for house in houses}

    # Add constraints that each attribute must be one of the allowed values
    for house in houses:
        s.add(Or([name_vars[house] == name for name in names]))
        s.add(Or([hair_vars[house] == color for color in hair_colors]))
        s.add(Or([music_vars[house] == genre for genre in music_genres]))

    # Add uniqueness constraints for each attribute across houses
    for name in names:
        s.add(Sum([If(name_vars[house] == name, 1, 0) for house in houses]) == 1)
    for color in hair_colors:
        s.add(Sum([If(hair_vars[house] == color, 1, 0) for house in houses]) == 1)
    for genre in music_genres:
        s.add(Sum([If(music_vars[house] == genre, 1, 0) for house in houses]) == 1)

    # Add constraints based on the clues
    # Clue 1: Eric is the person who has red hair.
    for house in houses:
        s.add(Implies(name_vars[house] == "Eric", hair_vars[house] == "red"))

    # Clue 2: The person who loves classical music is directly left of the person who has blonde hair.
    for i in range(1, 4):
        s.add(Implies(music_vars[i] == "classical", hair_vars[i+1] == "blonde"))

    # Clue 3: The person who has brown hair is not in the first house.
    s.add(hair_vars[1] != "brown")

    # Clue 4: The person who loves pop music is not in the third house.
    s.add(music_vars[3] != "pop")

    # Clue 5: The person who loves classical music is in the first house.
    s.add(music_vars[1] == "classical")

    # Clue 6: The person who loves jazz music is the person who has red hair.
    for house in houses:
        s.add(Implies(music_vars[house] == "jazz", hair_vars[house] == "red"))

    # Clue 7: The person who loves rock music is Arnold.
    for house in houses:
        s.add(Implies(music_vars[house] == "rock", name_vars[house] == "Arnold"))

    # Clue 8: Peter is somewhere to the right of the person who loves rock music.
    # Find the house with rock music and ensure Peter is in a higher-numbered house.
    rock_house = Int("rock_house")
    s.add(rock_house >= 1, rock_house <= 4)
    for house in houses:
        s.add(Implies(music_vars[house] == "rock", rock_house == house))
    for house in houses:
        s.add(Implies(name_vars[house] == "Peter", house > rock_house))

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "HairColor", "MusicGenre"],
                "rows": []
            }
        }
        for house in sorted(houses):
            name = model.eval(name_vars[house]).as_string()
            hair = model.eval(hair_vars[house]).as_string()
            music = model.eval(music_vars[house]).as_string()
            solution["solution"]["rows"].append([str(house), name, hair, music])
        return solution
    else:
        return {"solution": {"header": ["House", "Name", "HairColor", "MusicGenre"], "rows": []}}

# Print the solution as JSON
import json
print(json.dumps(solve_scheduling_problem(), indent=2))