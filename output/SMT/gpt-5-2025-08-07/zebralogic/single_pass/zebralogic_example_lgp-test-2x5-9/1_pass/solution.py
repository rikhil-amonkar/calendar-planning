from z3 import Solver, Int, Distinct, And, Or, sat
import json

def make_category_vars(values, prefix):
    return {val: Int(f"{prefix}_{i}") for i, val in enumerate(values)}

def main():
    # Houses are indexed 0 and 1 (representing house "1" and "2")
    houses = [0, 1]

    # Categories and values
    names = ["Arnold", "Eric"]
    book_genres = ["science fiction", "mystery"]
    vacations = ["mountain", "beach"]
    animals = ["cat", "horse"]
    music_genres = ["rock", "pop"]

    # Create Z3 variables mapping each value to a house index
    name_vars = make_category_vars(names, "name")
    book_vars = make_category_vars(book_genres, "book")
    vacation_vars = make_category_vars(vacations, "vac")
    animal_vars = make_category_vars(animals, "animal")
    music_vars = make_category_vars(music_genres, "music")

    s = Solver()

    # Domain constraints: each variable must be 0 or 1 (house index)
    for d in (name_vars, book_vars, vacation_vars, animal_vars, music_vars):
        for v in d.values():
            s.add(Or(v == houses[0], v == houses[1]))

    # Uniqueness constraints within each category (each house has exactly one of each)
    s.add(Distinct(*name_vars.values()))
    s.add(Distinct(*book_vars.values()))
    s.add(Distinct(*vacation_vars.values()))
    s.add(Distinct(*animal_vars.values()))
    s.add(Distinct(*music_vars.values()))

    # Clues:
    # 1. The person who loves beach vacations is Eric.
    s.add(vacation_vars["beach"] == name_vars["Eric"])

    # 2. The person who loves pop music is the person who loves beach vacations.
    s.add(music_vars["pop"] == vacation_vars["beach"])

    # 3. The person who loves rock music is the person who loves mystery books.
    s.add(music_vars["rock"] == book_vars["mystery"])

    # 4. The cat lover is not in the second house. (house index 1)
    s.add(animal_vars["cat"] != 1)

    # 5. The person who loves mystery books is in the first house. (house index 0)
    s.add(book_vars["mystery"] == 0)

    assert s.check() == sat
    m = s.model()

    # Helper to find which value is at a given house for a category
    def value_at_house(var_map, house_index):
        for val, var in var_map.items():
            if m[var].as_long() == house_index:
                return val
        return None  # should not happen

    rows = []
    for i in houses:
        row = [
            str(i + 1),
            value_at_house(name_vars, i),
            value_at_house(book_vars, i),
            value_at_house(vacation_vars, i),
            value_at_house(animal_vars, i),
            value_at_house(music_vars, i),
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()