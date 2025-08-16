import json
from z3 import Int, Distinct, Solver, And

def solve_puzzle():
    houses = [1, 2, 3, 4]

    Names = ["Peter", "Alice", "Eric", "Arnold"]
    Hobbies = ["cooking", "painting", "gardening", "photography"]
    Animals = ["horse", "fish", "cat", "bird"]
    BookGenres = ["fantasy", "mystery", "romance", "science fiction"]
    Birthdays = ["april", "jan", "sept", "feb"]
    MusicGenres = ["pop", "rock", "classical", "jazz"]

    # Create position variables (house index 1..4) for each attribute value
    def mk_vars(values, prefix):
        return {v: Int(f"{prefix}_{v.replace(' ', '_')}") for v in values}

    pos_name = mk_vars(Names, "name")
    pos_hobby = mk_vars(Hobbies, "hobby")
    pos_animal = mk_vars(Animals, "animal")
    pos_book = mk_vars(BookGenres, "book")
    pos_bday = mk_vars(Birthdays, "bday")
    pos_music = mk_vars(MusicGenres, "music")

    s = Solver()

    # Domains
    for d in [pos_name, pos_hobby, pos_animal, pos_book, pos_bday, pos_music]:
        for v in d.values():
            s.add(And(v >= 1, v <= 4))

    # All-different for each category
    s.add(Distinct([pos_name[n] for n in Names]))
    s.add(Distinct([pos_hobby[h] for h in Hobbies]))
    s.add(Distinct([pos_animal[a] for a in Animals]))
    s.add(Distinct([pos_book[b] for b in BookGenres]))
    s.add(Distinct([pos_bday[b] for b in Birthdays]))
    s.add(Distinct([pos_music[m] for m in MusicGenres]))

    # Clues constraints
    # 1. cooking == romance
    s.add(pos_hobby["cooking"] == pos_book["romance"])
    # 2. feb == pop
    s.add(pos_bday["feb"] == pos_music["pop"])
    # 3. Eric != house 2
    s.add(pos_name["Eric"] != 2)
    # 4. romance != house 4
    s.add(pos_book["romance"] != 4)
    # 5. feb == fish
    s.add(pos_bday["feb"] == pos_animal["fish"])
    # 6. Alice right of fantasy
    s.add(pos_name["Alice"] > pos_book["fantasy"])
    # 7. horse == rock
    s.add(pos_animal["horse"] == pos_music["rock"])
    # 8. gardening == April
    s.add(pos_hobby["gardening"] == pos_bday["april"])
    # 9. jazz == cooking
    s.add(pos_music["jazz"] == pos_hobby["cooking"])
    # 10. rock == mystery
    s.add(pos_music["rock"] == pos_book["mystery"])
    # 11. painting directly left of romance
    s.add(pos_hobby["painting"] + 1 == pos_book["romance"])
    # 12. Peter == pop
    s.add(pos_name["Peter"] == pos_music["pop"])
    # 13. gardening == Arnold
    s.add(pos_hobby["gardening"] == pos_name["Arnold"])
    # 14. rock directly left of Jan
    s.add(pos_music["rock"] + 1 == pos_bday["jan"])
    # 15. cooking != house 3
    s.add(pos_hobby["cooking"] != 3)
    # 16. cat right of horse
    s.add(pos_animal["cat"] > pos_animal["horse"])

    assert s.check().r == 1, "Puzzle has no solution or is not uniquely solvable with the given constraints."
    m = s.model()

    # Invert position maps to house -> value
    def invert(pos_map, values):
        house_to_val = {}
        for v in values:
            house_to_val[m[pos_map[v]].as_long()] = v
        return house_to_val

    name_at = invert(pos_name, Names)
    hobby_at = invert(pos_hobby, Hobbies)
    animal_at = invert(pos_animal, Animals)
    book_at = invert(pos_book, BookGenres)
    bday_at = invert(pos_bday, Birthdays)
    music_at = invert(pos_music, MusicGenres)

    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
            "rows": []
        }
    }

    for h in houses:
        row = [
            str(h),
            name_at[h],
            hobby_at[h],
            animal_at[h],
            book_at[h],
            bday_at[h],
            music_at[h]
        ]
        solution["solution"]["rows"].append(row)

    return solution

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))