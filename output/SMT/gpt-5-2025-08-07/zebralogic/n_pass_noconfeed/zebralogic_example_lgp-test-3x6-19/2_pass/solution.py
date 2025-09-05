import json
from z3 import Solver, Int, Distinct, And, sat

def main():
    houses = [1, 2, 3]

    # Categories and values
    Names = ["Arnold", "Eric", "Peter"]
    Cigars = ["pall mall", "blue master", "prince"]
    Animals = ["horse", "cat", "bird"]
    Children = ["Bella", "Fred", "Meredith"]
    BookGenres = ["science fiction", "romance", "mystery"]
    Phones = ["google pixel 6", "iphone 13", "samsung galaxy s21"]

    # Create Z3 Int variables for each item indicating the house position (1..3)
    def mk_vars(prefix, items):
        return {item: Int(f"{prefix}_{item.replace(' ', '_').replace('-', '_')}") for item in items}

    name_pos = mk_vars("Name", Names)
    cigar_pos = mk_vars("Cigar", Cigars)
    animal_pos = mk_vars("Animal", Animals)
    child_pos = mk_vars("Child", Children)
    book_pos = mk_vars("Book", BookGenres)
    phone_pos = mk_vars("Phone", Phones)

    s = Solver()

    # Domain constraints: each item occupies a house 1..3
    for d in [name_pos, cigar_pos, animal_pos, child_pos, book_pos, phone_pos]:
        for v in d.values():
            s.add(And(v >= 1, v <= 3))

    # Uniqueness within each category
    s.add(Distinct([name_pos[n] for n in Names]))
    s.add(Distinct([cigar_pos[c] for c in Cigars]))
    s.add(Distinct([animal_pos[a] for a in Animals]))
    s.add(Distinct([child_pos[c] for c in Children]))
    s.add(Distinct([book_pos[b] for b in BookGenres]))
    s.add(Distinct([phone_pos[p] for p in Phones]))

    # Clues as constraints
    # 1. The person who loves mystery books is the person's child is named Fred.
    s.add(book_pos["mystery"] == child_pos["Fred"])

    # 2. The cat lover is Eric.
    s.add(animal_pos["cat"] == name_pos["Eric"])

    # 3. The person partial to Pall Mall is in the second house.
    s.add(cigar_pos["pall mall"] == 2)

    # 4. The person who keeps horses is the person's child is named Meredith.
    s.add(animal_pos["horse"] == child_pos["Meredith"])

    # 5. The person's child is named Bella is the Prince smoker.
    s.add(child_pos["Bella"] == cigar_pos["prince"])

    # 6. The person who uses an iPhone 13 is directly left of the person who uses a Samsung Galaxy S21.
    s.add(phone_pos["iphone 13"] + 1 == phone_pos["samsung galaxy s21"])

    # 7. The person's child is named Fred is directly left of Arnold.
    s.add(child_pos["Fred"] + 1 == name_pos["Arnold"])

    # 8. Peter is somewhere to the left of Eric.
    s.add(name_pos["Peter"] < name_pos["Eric"])

    # 9. The person who loves science fiction books is the person who uses a Samsung Galaxy S21.
    s.add(book_pos["science fiction"] == phone_pos["samsung galaxy s21"])

    # 10. The person who loves science fiction books is in the third house.
    s.add(book_pos["science fiction"] == 3)

    # 11. The person who loves mystery books is not in the second house.
    s.add(book_pos["mystery"] != 2)

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Helper: invert mapping from item->position to position->item
    def invert(pos_map, items):
        inv = {}
        for it in items:
            inv[int(m[pos_map[it]].as_long())] = it
        return inv

    name_at = invert(name_pos, Names)
    cigar_at = invert(cigar_pos, Cigars)
    animal_at = invert(animal_pos, Animals)
    child_at = invert(child_pos, Children)
    book_at = invert(book_pos, BookGenres)
    phone_at = invert(phone_pos, Phones)

    header = ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"]
    rows = []
    for h in houses:
        row = [
            str(h),
            name_at[h],
            cigar_at[h],
            animal_at[h],
            child_at[h],
            book_at[h],
            phone_at[h],
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
    main()