from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    s = Solver()

    # Define the houses
    houses = [1, 2, 3, 4, 5, 6]

    # Define the names and music genres
    names = ["Arnold", "Eric", "Peter", "Alice", "Carol", "Bob"]
    genres = ["jazz", "pop", "classical", "rock", "hip hop", "country"]

    # Create variables for each house's name and music genre
    name_vars = [Int(f"name_{h}") for h in houses]
    genre_vars = [Int(f"genre_{h}") for h in houses]

    # Add constraints for names and genres to be within their respective ranges
    for h in houses:
        s.add(And(name_vars[h-1] >= 0, name_vars[h-1] < len(names)))
        s.add(And(genre_vars[h-1] >= 0, genre_vars[h-1] < len(genres)))

    # Add constraint that all names are distinct
    s.add(Distinct(name_vars))

    # Add constraint that all genres are distinct
    s.add(Distinct(genre_vars))

    # Clue 3: Carol is in the sixth house
    s.add(name_vars[5] == names.index("Carol"))

    # Clue 5: The person who loves country music is Carol
    # So, the genre of house 6 is country
    s.add(genre_vars[5] == genres.index("country"))

    # Clue 9: The person who loves hip-hop music is in the third house
    s.add(genre_vars[2] == genres.index("hip hop"))

    # Clue 8: The person who loves pop music is Peter
    # So, for any house, if genre is pop, then name is Peter, and vice versa
    for h in houses:
        s.add(Implies(genre_vars[h-1] == genres.index("pop"), name_vars[h-1] == names.index("Peter")))
        s.add(Implies(name_vars[h-1] == names.index("Peter"), genre_vars[h-1] == genres.index("pop")))

    # Clue 10: There is one house between Peter and Bob
    # This means if Peter is in house X, Bob is in house X+2, or vice versa
    # Since Bob is to the left of jazz (Clue 1), and jazz is to the right of Bob, Bob cannot be in house 5 or 6
    # So possible positions for Peter: 1, 2, 3 (since Bob would then be in 3, 4, 5)
    # But hip-hop is in house 3 (Clue 9), and Bob is to the left of jazz (Clue 1), so let's explore possibilities
    # We'll add a constraint that for some house h, name is Peter and name[h+2] is Bob
    # Or name is Bob and name[h+2] is Peter, but given Bob is left of jazz, Peter is likely left of Bob
    s.add(Or(
        And(name_vars[0] == names.index("Peter"), name_vars[2] == names.index("Bob")),
        And(name_vars[1] == names.index("Peter"), name_vars[3] == names.index("Bob")),
        And(name_vars[2] == names.index("Peter"), name_vars[4] == names.index("Bob"))
    ))

    # Clue 1: Bob is directly left of the person who loves jazz music
    # So Bob is in house h, jazz is in house h+1
    s.add(Or(
        And(name_vars[0] == names.index("Bob"), genre_vars[1] == genres.index("jazz")),
        And(name_vars[1] == names.index("Bob"), genre_vars[2] == genres.index("jazz")),
        And(name_vars[2] == names.index("Bob"), genre_vars[3] == genres.index("jazz")),
        And(name_vars[3] == names.index("Bob"), genre_vars[4] == genres.index("jazz")),
        And(name_vars[4] == names.index("Bob"), genre_vars[5] == genres.index("jazz"))
    ))

    # Clue 2: Eric is somewhere to the left of the person who loves hip-hop music
    # Hip-hop is in house 3, so Eric is in house 1 or 2
    s.add(Or(
        name_vars[0] == names.index("Eric"),
        name_vars[1] == names.index("Eric")
    ))

    # Clue 4: Eric and the person who loves hip-hop music are next to each other
    # Hip-hop is in house 3, so Eric is in house 2 or 4
    # But from Clue 2, Eric is left of hip-hop (house 3), so Eric must be in house 2
    s.add(name_vars[1] == names.index("Eric"))

    # Clue 6: Arnold is not in the fifth house
    s.add(name_vars[4] != names.index("Arnold"))

    # Clue 7: Arnold is somewhere to the right of the person who loves pop music
    # Pop is Peter, so Arnold is to the right of Peter
    # We need to find Peter's position and ensure Arnold is to the right
    # We'll add that for all houses, if genre is pop, then Arnold is in a higher-numbered house
    for h_peter in houses:
        for h_arnold in houses:
            if h_arnold > h_peter:
                s.add(Implies(
                    genre_vars[h_peter-1] == genres.index("pop"),
                    Or([name_vars[h-1] == names.index("Arnold") for h in range(h_peter+1, 7)])
                ))

    # Clue 11: The person who loves rock music is not in the fifth house
    s.add(genre_vars[4] != genres.index("rock"))

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "MusicGenre"],
                "rows": []
            }
        }
        for h in houses:
            name_index = model.evaluate(name_vars[h-1]).as_long()
            genre_index = model.evaluate(genre_vars[h-1]).as_long()
            solution["solution"]["rows"].append([
                str(h),
                names[name_index],
                genres[genre_index]
            ])
        return solution
    else:
        return {"error": "No solution found"}

# Output the solution in the required JSON format
import json
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))