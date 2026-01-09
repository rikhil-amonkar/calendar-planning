import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = range(1, 7)

    names = ["Arnold", "Eric", "Peter", "Alice", "Carol", "Bob"]
    genres = ["jazz", "pop", "classical", "rock", "hip hop", "country"]

    problem = Problem()

    # Variables: each name and each genre maps to a house number 1..6
    problem.addVariables(names, houses)
    problem.addVariables(genres, houses)

    # All-different constraints within each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), genres)

    # 1. Bob is directly left of the person who loves jazz music.
    problem.addConstraint(lambda b, j: b == j - 1, ("Bob", "jazz"))

    # 2. Eric is somewhere to the left of the person who loves hip-hop music.
    problem.addConstraint(lambda e, h: e < h, ("Eric", "hip hop"))

    # 3. Carol is in the sixth house.
    problem.addConstraint(lambda c: c == 6, ("Carol",))

    # 4. Eric and the person who loves hip-hop music are next to each other.
    problem.addConstraint(lambda e, h: abs(e - h) == 1, ("Eric", "hip hop"))

    # 5. The person who loves country music is Carol.
    problem.addConstraint(lambda country, carol: country == carol, ("country", "Carol"))

    # 6. Arnold is not in the fifth house.
    problem.addConstraint(lambda a: a != 5, ("Arnold",))

    # 7. Arnold is somewhere to the right of the person who loves pop music.
    problem.addConstraint(lambda a, p: a > p, ("Arnold", "pop"))

    # 8. The person who loves pop music is Peter.
    problem.addConstraint(lambda p, peter: p == peter, ("pop", "Peter"))

    # 9. The person who loves hip-hop music is in the third house.
    problem.addConstraint(lambda h: h == 3, ("hip hop",))

    # 10. There is one house between Peter and Bob.
    problem.addConstraint(lambda peter, bob: abs(peter - bob) == 2, ("Peter", "Bob"))

    # 11. The person who loves rock music is not in the fifth house.
    problem.addConstraint(lambda r: r != 5, ("rock",))

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given constraints.")

    # Assuming uniqueness; take the first solution
    sol = solutions[0]

    # Build house to name and house to genre mappings
    house_to_name = {sol[name]: name for name in names}
    house_to_genre = {sol[genre]: genre for genre in genres}

    result = {
        "solution": {
            "header": ["House", "Name", "MusicGenre"],
            "rows": []
        }
    }

    for h in range(1, 7):
        row = [str(h), house_to_name[h], house_to_genre[h]]
        result["solution"]["rows"].append(row)

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()