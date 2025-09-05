import json
from z3 import Solver, Int, And, Distinct, sat

def solve_puzzle():
    # Define houses
    houses = [1, 2]
    num_houses = len(houses)

    # Attributes and their possible values
    Names = ["Arnold", "Eric"]
    BookGenres = ["science fiction", "mystery"]
    Vacations = ["mountain", "beach"]
    Animals = ["cat", "horse"]
    MusicGenres = ["rock", "pop"]

    # Create Z3 variables: each option maps to a house number
    def create_vars(options, prefix):
        vars_list = []
        for opt in options:
            v = Int(f"{prefix}_{opt.replace(' ', '_')}")
            vars_list.append(v)
        return vars_list

    name_vars = create_vars(Names, "Name")
    book_vars = create_vars(BookGenres, "Book")
    vacation_vars = create_vars(Vacations, "Vacation")
    animal_vars = create_vars(Animals, "Animal")
    music_vars = create_vars(MusicGenres, "Music")

    # Helper to get variable by option
    def var_of(options, vars_list, option_value):
        idx = options.index(option_value)
        return vars_list[idx]

    s = Solver()

    # Domain constraints: every variable is in 1..num_houses
    for v in name_vars + book_vars + vacation_vars + animal_vars + music_vars:
        s.add(And(v >= 1, v <= num_houses))

    # Uniqueness constraints within each attribute category
    s.add(Distinct(*name_vars))
    s.add(Distinct(*book_vars))
    s.add(Distinct(*vacation_vars))
    s.add(Distinct(*animal_vars))
    s.add(Distinct(*music_vars))

    # Clues:
    # 1. The person who loves beach vacations is Eric.
    s.add(var_of(Vacations, vacation_vars, "beach") == var_of(Names, name_vars, "Eric"))

    # 2. The person who loves pop music is the person who loves beach vacations.
    s.add(var_of(MusicGenres, music_vars, "pop") == var_of(Vacations, vacation_vars, "beach"))

    # 3. The person who loves rock music is the person who loves mystery books.
    s.add(var_of(MusicGenres, music_vars, "rock") == var_of(BookGenres, book_vars, "mystery"))

    # 4. The cat lover is not in the second house.
    s.add(var_of(Animals, animal_vars, "cat") != 2)

    # 5. The person who loves mystery books is in the first house.
    s.add(var_of(BookGenres, book_vars, "mystery") == 1)

    if s.check() != sat:
        raise Exception("No solution found")

    m = s.model()

    # Build the solution rows by house
    def option_at_house(options, vars_list, house):
        for opt, v in zip(options, vars_list):
            if m[v].as_long() == house:
                return opt
        return None

    rows = []
    for h in houses:
        name = option_at_house(Names, name_vars, h)
        book = option_at_house(BookGenres, book_vars, h)
        vacation = option_at_house(Vacations, vacation_vars, h)
        animal = option_at_house(Animals, animal_vars, h)
        music = option_at_house(MusicGenres, music_vars, h)
        rows.append([str(h), name, book, vacation, animal, music])

    result = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))