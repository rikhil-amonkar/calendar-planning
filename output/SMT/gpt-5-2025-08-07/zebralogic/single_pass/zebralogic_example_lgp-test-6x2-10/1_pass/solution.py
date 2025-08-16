import json
from z3 import Int, Solver, And, Distinct, Abs, sat

def solve_puzzle():
    # Domains
    houses = range(1, 7)
    names = ["Arnold", "Eric", "Peter", "Alice", "Carol", "Bob"]
    genres = ["jazz", "pop", "classical", "rock", "hip hop", "country"]

    # Variables: position (house number) for each name and genre
    pos_name = {n: Int(f"pos_name_{n.lower()}") for n in names}
    pos_genre = {g: Int(f"pos_genre_{g.replace(' ', '_')}") for g in genres}

    s = Solver()

    # Bounds: all positions are between 1 and 6
    for v in list(pos_name.values()) + list(pos_genre.values()):
        s.add(And(v >= 1, v <= 6))

    # Uniqueness: all names in distinct houses; all genres in distinct houses
    s.add(Distinct(*pos_name.values()))
    s.add(Distinct(*pos_genre.values()))

    # Clues:
    # 1. Bob is directly left of the person who loves jazz music.
    s.add(pos_name["Bob"] + 1 == pos_genre["jazz"])

    # 2. Eric is somewhere to the left of the person who loves hip hop music.
    s.add(pos_name["Eric"] < pos_genre["hip hop"])

    # 3. Carol is in the sixth house.
    s.add(pos_name["Carol"] == 6)

    # 4. Eric and the person who loves hip hop music are next to each other.
    s.add(Abs(pos_name["Eric"] - pos_genre["hip hop"]) == 1)

    # 5. The person who loves country music is Carol.
    s.add(pos_genre["country"] == pos_name["Carol"])

    # 6. Arnold is not in the fifth house.
    s.add(pos_name["Arnold"] != 5)

    # 7. Arnold is somewhere to the right of the person who loves pop music.
    s.add(pos_name["Arnold"] > pos_genre["pop"])

    # 8. The person who loves pop music is Peter.
    s.add(pos_genre["pop"] == pos_name["Peter"])

    # 9. The person who loves hip hop music is in the third house.
    s.add(pos_genre["hip hop"] == 3)

    # 10. There is one house between Peter and Bob.
    s.add(Abs(pos_name["Peter"] - pos_name["Bob"]) == 2)

    # 11. The person who loves rock music is not in the fifth house.
    s.add(pos_genre["rock"] != 5)

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Build mapping from house -> name and genre
    house_to_name = {}
    house_to_genre = {}

    for n in names:
        house_to_name[m[pos_name[n]].as_long()] = n
    for g in genres:
        house_to_genre[m[pos_genre[g]].as_long()] = g

    rows = []
    for h in houses:
        rows.append([str(h), house_to_name[h], house_to_genre[h]])

    result = {
        "solution": {
            "header": ["House", "Name", "MusicGenre"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))