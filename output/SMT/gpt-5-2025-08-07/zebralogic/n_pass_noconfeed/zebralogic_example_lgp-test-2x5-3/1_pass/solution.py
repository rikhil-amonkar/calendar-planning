import json
from z3 import Int, Solver, Distinct, And, Or, Not, sat

def solve_puzzle():
    # Domain values
    houses = [1, 2]  # indices will be 0..1; displayed as "1","2"
    Names = ["Eric", "Arnold"]
    Hobbies = ["gardening", "photography"]
    BookGenres = ["science fiction", "mystery"]
    MusicGenres = ["rock", "pop"]
    Birthdays = ["april", "sept"]

    # Index helpers
    name_idx = {v: i for i, v in enumerate(Names)}
    hobby_idx = {v: i for i, v in enumerate(Hobbies)}
    book_idx = {v: i for i, v in enumerate(BookGenres)}
    music_idx = {v: i for i, v in enumerate(MusicGenres)}
    bday_idx = {v: i for i, v in enumerate(Birthdays)}

    # Z3 variables per house
    n = len(houses)
    name = [Int(f"name_{i}") for i in range(n)]
    hobby = [Int(f"hobby_{i}") for i in range(n)]
    book = [Int(f"book_{i}") for i in range(n)]
    music = [Int(f"music_{i}") for i in range(n)]
    bday = [Int(f"bday_{i}") for i in range(n)]

    s = Solver()

    # Domain constraints
    for i in range(n):
        s.add(And(name[i] >= 0, name[i] < len(Names)))
        s.add(And(hobby[i] >= 0, hobby[i] < len(Hobbies)))
        s.add(And(book[i] >= 0, book[i] < len(BookGenres)))
        s.add(And(music[i] >= 0, music[i] < len(MusicGenres)))
        s.add(And(bday[i] >= 0, bday[i] < len(Birthdays)))

    # Uniqueness constraints across houses for each attribute
    s.add(Distinct(name))
    s.add(Distinct(hobby))
    s.add(Distinct(book))
    s.add(Distinct(music))
    s.add(Distinct(bday))

    # Clues:
    # 1. The person who loves mystery books is the person who loves rock music.
    for i in range(n):
        s.add((book[i] == book_idx["mystery"]) == (music[i] == music_idx["rock"]))

    # 2. Arnold is not in the first house.
    s.add(name[0] != name_idx["Arnold"])

    # 3. The person who loves mystery books is the person who enjoys gardening.
    for i in range(n):
        s.add((book[i] == book_idx["mystery"]) == (hobby[i] == hobby_idx["gardening"]))

    # 4. The person whose birthday is in April is Arnold.
    for i in range(n):
        s.add((bday[i] == bday_idx["april"]) == (name[i] == name_idx["Arnold"]))

    # 5. The person who loves mystery books is in the first house.
    s.add(book[0] == book_idx["mystery"])

    # Solve
    if s.check() != sat:
        raise RuntimeError("Puzzle is unsatisfiable")

    m = s.model()

    # Build solution rows
    rows = []
    for i in range(n):
        row = [
            str(houses[i]),
            Names[m[name[i]].as_long()],
            Hobbies[m[hobby[i]].as_long()],
            BookGenres[m[book[i]].as_long()],
            MusicGenres[m[music[i]].as_long()],
            Birthdays[m[bday[i]].as_long()],
        ]
        rows.append(row)

    result = {
        "solution": {
            "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))