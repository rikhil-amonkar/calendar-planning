import json
from z3 import Int, Solver, And, Or, Distinct, sat

def solve_puzzle():
    # Houses numbered 1..6
    houses = list(range(1, 7))

    # Attributes
    names = ["Arnold", "Eric", "Peter", "Alice", "Carol", "Bob"]
    genres = ["jazz", "pop", "classical", "rock", "hip hop", "country"]

    # Variables: position (house number) for each name and genre
    pos_name = {n: Int(f"pos_name_{n}") for n in names}
    pos_genre = {g: Int(f"pos_genre_{g.replace(' ', '_')}") for g in genres}

    s = Solver()

    # Domain constraints: each position is between 1 and 6
    for v in list(pos_name.values()) + list(pos_genre.values()):
        s.add(And(v >= 1, v <= 6))

    # Uniqueness constraints
    s.add(Distinct([pos_name[n] for n in names]))
    s.add(Distinct([pos_genre[g] for g in genres]))

    # Clues:
    # 1. Bob is directly left of the person who loves jazz music.
    s.add(pos_name["Bob"] + 1 == pos_genre["jazz"])

    # 2. Eric is somewhere to the left of the person who loves hip-hop music.
    # 4. Eric and the person who loves hip-hop music are next to each other.
    # Combined -> Eric is directly left of hip hop.
    s.add(pos_name["Eric"] + 1 == pos_genre["hip hop"])

    # 3. Carol is in the sixth house.
    s.add(pos_name["Carol"] == 6)

    # 5. The person who loves country music is Carol.
    s.add(pos_genre["country"] == pos_name["Carol"])

    # 6. Arnold is not in the fifth house.
    s.add(pos_name["Arnold"] != 5)

    # 7. Arnold is somewhere to the right of the person who loves pop music.
    # 8. The person who loves pop music is Peter.
    s.add(pos_genre["pop"] == pos_name["Peter"])
    s.add(pos_name["Arnold"] > pos_genre["pop"])

    # 9. The person who loves hip-hop music is in the third house.
    s.add(pos_genre["hip hop"] == 3)

    # 10. There is one house between Peter and Bob.
    s.add(Or(pos_name["Peter"] + 2 == pos_name["Bob"], pos_name["Bob"] + 2 == pos_name["Peter"]))

    # 11. The person who loves rock music is not in the fifth house.
    s.add(pos_genre["rock"] != 5)

    # Solve
    if s.check() != sat:
        raise Exception("Puzzle is unsatisfiable with given constraints.")

    m = s.model()

    # Build inverse mappings
    name_by_house = {h: None for h in houses}
    genre_by_house = {h: None for h in houses}

    for n in names:
        h = m.eval(pos_name[n]).as_long()
        name_by_house[h] = n

    for g in genres:
        h = m.eval(pos_genre[g]).as_long()
        genre_by_house[h] = g

    # Prepare JSON output
    rows = []
    for h in houses:
        rows.append([str(h), name_by_house[h], genre_by_house[h]])

    result = {
        "solution": {
            "header": ["House", "Name", "MusicGenre"],
            "rows": rows
        }
    }

    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))