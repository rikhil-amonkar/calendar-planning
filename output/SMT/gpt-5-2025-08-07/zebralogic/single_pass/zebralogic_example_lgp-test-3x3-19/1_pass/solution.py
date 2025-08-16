import json
from z3 import Int, Solver, Distinct, And

def solve_puzzle():
    houses = [1, 2, 3]

    names = ["Eric", "Arnold", "Peter"]
    smoothies = ["desert", "watermelon", "cherry"]
    genres = ["science fiction", "romance", "mystery"]

    # Helper maps to indices
    name_idx = {n: i for i, n in enumerate(names)}
    smoothie_idx = {s: i for i, s in enumerate(smoothies)}
    genre_idx = {g: i for i, g in enumerate(genres)}

    # Variables: position (house number) of each attribute
    NamePos = {n: Int(f"NamePos_{n}") for n in names}
    SmoothiePos = {s: Int(f"SmoothiePos_{s}") for s in smoothies}
    GenrePos = {g: Int(f"GenrePos_{g}") for g in genres}

    s = Solver()

    # Domain constraints (1..3)
    for v in list(NamePos.values()) + list(SmoothiePos.values()) + list(GenrePos.values()):
        s.add(And(v >= 1, v <= 3))

    # All-different within each category
    s.add(Distinct(*NamePos.values()))
    s.add(Distinct(*SmoothiePos.values()))
    s.add(Distinct(*GenrePos.values()))

    # Clues:
    # 1. Cherry smoothies is somewhere to the left of mystery books.
    s.add(SmoothiePos["cherry"] < GenrePos["mystery"])

    # 2. Arnold is the person who loves mystery books.
    s.add(NamePos["Arnold"] == GenrePos["mystery"])

    # 3. Science fiction books is not in the first house.
    s.add(GenrePos["science fiction"] != 1)

    # 4. The Desert smoothie lover is directly left of the person who loves mystery books.
    s.add(SmoothiePos["desert"] + 1 == GenrePos["mystery"])

    # 5. Peter is in the first house.
    s.add(NamePos["Peter"] == 1)

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Build reverse lookup for each house
    house_to_name = {m.evaluate(pos).as_long(): name for name, pos in NamePos.items()}
    house_to_smoothie = {m.evaluate(pos).as_long(): sm for sm, pos in SmoothiePos.items()}
    house_to_genre = {m.evaluate(pos).as_long(): gn for gn, pos in GenrePos.items()}

    rows = []
    for h in houses:
        rows.append([
            str(h),
            house_to_name[h],
            house_to_smoothie[h],
            house_to_genre[h]
        ])

    result = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "BookGenre"],
            "rows": rows
        }
    }
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()