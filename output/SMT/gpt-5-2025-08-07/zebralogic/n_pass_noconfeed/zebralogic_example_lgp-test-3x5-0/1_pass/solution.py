import json
from z3 import Solver, Int, And, Or, Distinct, Implies, sat

def solve_puzzle():
    # Domains and indices
    houses = range(3)

    Names = ["Peter", "Arnold", "Eric"]
    Books = ["science fiction", "mystery", "romance"]
    Smoothies = ["watermelon", "desert", "cherry"]
    Birthdays = ["april", "jan", "sept"]
    Heights = ["average", "very short", "short"]

    name_idx = {v: i for i, v in enumerate(Names)}
    book_idx = {v: i for i, v in enumerate(Books)}
    smoothie_idx = {v: i for i, v in enumerate(Smoothies)}
    birthday_idx = {v: i for i, v in enumerate(Birthdays)}
    height_idx = {v: i for i, v in enumerate(Heights)}

    # Z3 variables: each is an Int for each house
    Name = [Int(f"Name_{i}") for i in houses]
    Book = [Int(f"Book_{i}") for i in houses]
    Smoothie = [Int(f"Smoothie_{i}") for i in houses]
    Birthday = [Int(f"Birthday_{i}") for i in houses]
    Height = [Int(f"Height_{i}") for i in houses]

    s = Solver()

    # Domain constraints
    for arr in [Name, Book, Smoothie, Birthday, Height]:
        for v in arr:
            s.add(And(v >= 0, v < 3))

    # Uniqueness (all different across houses for each attribute)
    s.add(Distinct(Name))
    s.add(Distinct(Book))
    s.add(Distinct(Smoothie))
    s.add(Distinct(Birthday))
    s.add(Distinct(Height))

    # Clues:
    # 1. The person who likes Cherry smoothies is not in the second house.
    s.add(Smoothie[1] != smoothie_idx["cherry"])

    # 2. Arnold is the person who loves mystery books.
    for i in houses:
        s.add((Name[i] == name_idx["Arnold"]) == (Book[i] == book_idx["mystery"]))

    # 3. The person whose birthday is in January is not in the first house.
    s.add(Birthday[0] != birthday_idx["jan"])

    # 4. The person who is very short is the person who loves romance books.
    for i in houses:
        s.add((Height[i] == height_idx["very short"]) == (Book[i] == book_idx["romance"]))

    # 5. The person who loves mystery books is the person whose birthday is in September.
    for i in houses:
        s.add((Book[i] == book_idx["mystery"]) == (Birthday[i] == birthday_idx["sept"]))

    # 6. The person who has an average height is the Desert smoothie lover.
    for i in houses:
        s.add((Height[i] == height_idx["average"]) == (Smoothie[i] == smoothie_idx["desert"]))

    # 7. Eric is in the first house.
    s.add(Name[0] == name_idx["Eric"])

    # 8. The Watermelon smoothie lover is the person who is short.
    for i in houses:
        s.add((Smoothie[i] == smoothie_idx["watermelon"]) == (Height[i] == height_idx["short"]))

    # 9. The Watermelon smoothie lover is Eric.
    for i in houses:
        s.add((Smoothie[i] == smoothie_idx["watermelon"]) == (Name[i] == name_idx["Eric"]))

    # Solve
    if s.check() != sat:
        raise RuntimeError("Puzzle is unsatisfiable")

    m = s.model()

    # Build JSON solution
    header = ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"]
    rows = []
    for i in houses:
        row = [
            str(i + 1),
            Names[m[Name[i]].as_long()],
            Books[m[Book[i]].as_long()],
            Smoothies[m[Smoothie[i]].as_long()],
            Birthdays[m[Birthday[i]].as_long()],
            Heights[m[Height[i]].as_long()],
        ]
        rows.append(row)

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

    print(json.dumps(result, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_puzzle()