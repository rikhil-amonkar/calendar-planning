import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()

    houses = range(1, 7)

    names = ["Bob", "Arnold", "Carol", "Alice", "Peter", "Eric"]
    genres = ["romance", "historical fiction", "biography", "mystery", "fantasy", "science fiction"]
    occupations = ["artist", "doctor", "nurse", "engineer", "teacher", "lawyer"]

    # Add variables for each attribute with domain 1..6 (house numbers)
    for n in names:
        problem.addVariable(n, houses)
    for g in genres:
        problem.addVariable(g, houses)
    for o in occupations:
        problem.addVariable(o, houses)

    # Uniqueness constraints for each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), genres)
    problem.addConstraint(AllDifferentConstraint(), occupations)

    # Constraints based on clues:

    # 1. Alice is the person who loves fantasy books.
    problem.addConstraint(lambda alice, fantasy: alice == fantasy, ("Alice", "fantasy"))

    # 2. The person who loves mystery books and Bob are next to each other.
    problem.addConstraint(lambda mystery, bob: abs(mystery - bob) == 1, ("mystery", "Bob"))

    # 3. Carol is the person who loves mystery books.
    problem.addConstraint(lambda carol, mystery: carol == mystery, ("Carol", "mystery"))

    # 4. The person who is a lawyer is the person who loves fantasy books.
    problem.addConstraint(lambda lawyer, fantasy: lawyer == fantasy, ("lawyer", "fantasy"))

    # 5. Bob is not in the fifth house.
    problem.addConstraint(lambda bob: bob != 5, ("Bob",))

    # 6. Arnold is somewhere to the left of the person who is an engineer.
    problem.addConstraint(lambda arnold, engineer: arnold < engineer, ("Arnold", "engineer"))

    # 7. The person who is a nurse is directly left of Alice.
    problem.addConstraint(lambda nurse, alice: nurse + 1 == alice, ("nurse", "Alice"))

    # 8. The person who loves biography books is the person who is a teacher.
    problem.addConstraint(lambda bio, teacher: bio == teacher, ("biography", "teacher"))

    # 9. The person who loves historical fiction books is somewhere to the left of the person who is a teacher.
    problem.addConstraint(lambda hist, teacher: hist < teacher, ("historical fiction", "teacher"))

    # 10. The person who is a doctor is in the first house.
    problem.addConstraint(lambda doctor: doctor == 1, ("doctor",))

    # 11. The person who loves science fiction books is the person who is an artist.
    problem.addConstraint(lambda sf, artist: sf == artist, ("science fiction", "artist"))

    # 12. Eric is in the third house.
    problem.addConstraint(lambda eric: eric == 3, ("Eric",))

    # 13. The person who loves mystery books is not in the fifth house.
    problem.addConstraint(lambda mystery: mystery != 5, ("mystery",))

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found for the given puzzle.")

    # Assume unique or take the first solution
    sol = solutions[0]

    # Build rows ordered by house 1..6
    rows = []
    for house in range(1, 7):
        name_at_house = next(n for n in names if sol[n] == house)
        genre_at_house = next(g for g in genres if sol[g] == house)
        occupation_at_house = next(o for o in occupations if sol[o] == house)
        rows.append([str(house), name_at_house, genre_at_house, occupation_at_house])

    output = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Occupation"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))