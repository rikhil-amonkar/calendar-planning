import json
from z3 import *

def solve_puzzle():
    # Domains
    Names = ["Arnold", "Eric", "Peter"]
    MusicGenres = ["pop", "rock", "classical"]
    Children = ["Fred", "Meredith", "Bella"]
    BookGenres = ["mystery", "romance", "science fiction"]

    # Helper to get index
    def idx(lst, val):
        return lst.index(val)

    # Create Z3 variables for each house (0..2 correspond to houses 1..3)
    name = [Int(f"name_{i}") for i in range(3)]
    music = [Int(f"music_{i}") for i in range(3)]
    child = [Int(f"child_{i}") for i in range(3)]
    book = [Int(f"book_{i}") for i in range(3)]

    s = Solver()

    # Domain constraints: each attribute value in 0..2
    for i in range(3):
        s.add(And(name[i] >= 0, name[i] < 3))
        s.add(And(music[i] >= 0, music[i] < 3))
        s.add(And(child[i] >= 0, child[i] < 3))
        s.add(And(book[i] >= 0, book[i] < 3))

    # All attributes are unique across houses
    s.add(Distinct(name))
    s.add(Distinct(music))
    s.add(Distinct(child))
    s.add(Distinct(book))

    # Clues:

    # 1. Fred is directly left of the mystery books.
    fred = idx(Children, "Fred")
    mystery = idx(BookGenres, "mystery")
    s.add(Or(And(child[0] == fred, book[1] == mystery),
             And(child[1] == fred, book[2] == mystery)))

    # 2. Peter is in the first house.
    peter = idx(Names, "Peter")
    s.add(name[0] == peter)

    # 3. Mystery books = classical music (same house).
    classical = idx(MusicGenres, "classical")
    for i in range(3):
        s.add((book[i] == mystery) == (music[i] == classical))

    # 4. Science fiction books = child Meredith (same house).
    sci_fi = idx(BookGenres, "science fiction")
    meredith = idx(Children, "Meredith")
    for i in range(3):
        s.add((book[i] == sci_fi) == (child[i] == meredith))

    # 5. Eric is the one who loves mystery books.
    eric = idx(Names, "Eric")
    for i in range(3):
        s.add((name[i] == eric) == (book[i] == mystery))

    # 6. Rock music is somewhere to the right of romance books.
    rock = idx(MusicGenres, "rock")
    romance = idx(BookGenres, "romance")
    s.add(Or(
        And(book[0] == romance, Or(music[1] == rock, music[2] == rock)),
        And(book[1] == romance, music[2] == rock)
    ))

    assert s.check() == sat
    m = s.model()

    # Build the solution rows
    rows = []
    for i in range(3):
        row = [
            str(i + 1),
            Names[m.evaluate(name[i]).as_long()],
            MusicGenres[m.evaluate(music[i]).as_long()],
            Children[m.evaluate(child[i]).as_long()],
            BookGenres[m.evaluate(book[i]).as_long()],
        ]
        rows.append(row)

    result = {
        "solution": {
            "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    print(json.dumps(solve_puzzle()))