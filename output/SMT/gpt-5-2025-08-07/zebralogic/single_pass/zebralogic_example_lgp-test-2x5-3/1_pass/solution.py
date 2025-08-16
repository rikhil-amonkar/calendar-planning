import json
from z3 import Solver, Ints, Distinct, And, Or, sat

def solve_puzzle():
    # Domains
    houses = [0, 1]  # 0 -> House 1, 1 -> House 2

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
    birthday_idx = {v: i for i, v in enumerate(Birthdays)}

    # Variables per house: each variable is an int in 0..1 mapping to the index within its category
    name = [Ints(f"name_{h+1}")[0] for h in houses]
    hobby = [Ints(f"hobby_{h+1}")[0] for h in houses]
    book = [Ints(f"book_{h+1}")[0] for h in houses]
    music = [Ints(f"music_{h+1}")[0] for h in houses]
    birthday = [Ints(f"birthday_{h+1}")[0] for h in houses]

    s = Solver()

    # Domain constraints: each value must be either 0 or 1 (since we have 2 options per category)
    for vars_ in (name, hobby, book, music, birthday):
        for v in vars_:
            s.add(Or(v == 0, v == 1))

    # All-different constraints per category (each attribute used exactly once)
    s.add(Distinct(name))
    s.add(Distinct(hobby))
    s.add(Distinct(book))
    s.add(Distinct(music))
    s.add(Distinct(birthday))

    # Clues:
    # 1. The person who loves mystery books is the person who loves rock music.
    for h in houses:
        s.add((book[h] == book_idx["mystery"]) == (music[h] == music_idx["rock"]))

    # 2. Arnold is not in the first house.
    s.add(name[0] != name_idx["Arnold"])

    # 3. The person who loves mystery books is the person who enjoys gardening.
    for h in houses:
        s.add((book[h] == book_idx["mystery"]) == (hobby[h] == hobby_idx["gardening"]))

    # 4. The person whose birthday is in April is Arnold.
    for h in houses:
        s.add((birthday[h] == birthday_idx["april"]) == (name[h] == name_idx["Arnold"]))

    # 5. The person who loves mystery books is in the first house.
    s.add(book[0] == book_idx["mystery"])

    if s.check() != sat:
        raise RuntimeError("Puzzle is unsatisfiable")

    m = s.model()

    # Build solution rows in house order 1..2
    rows = []
    for h in houses:
        row = [
            str(h + 1),
            Names[m[name[h]].as_long()],
            Hobbies[m[hobby[h]].as_long()],
            BookGenres[m[book[h]].as_long()],
            MusicGenres[m[music[h]].as_long()],
            Birthdays[m[birthday[h]].as_long()],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()