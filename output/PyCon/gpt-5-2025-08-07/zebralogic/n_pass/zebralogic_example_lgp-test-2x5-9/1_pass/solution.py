import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    # Define houses and attributes
    houses = [1, 2]
    Names = ["Arnold", "Eric"]
    BookGenres = ["science fiction", "mystery"]
    Vacations = ["mountain", "beach"]
    Animals = ["cat", "horse"]
    MusicGenres = ["rock", "pop"]

    # Initialize problem
    problem = Problem()

    # Add variables for each attribute value with domain as houses
    for v in Names + BookGenres + Vacations + Animals + MusicGenres:
        problem.addVariable(v, houses)

    # Uniqueness constraints within each category
    problem.addConstraint(AllDifferentConstraint(), Names)
    problem.addConstraint(AllDifferentConstraint(), BookGenres)
    problem.addConstraint(AllDifferentConstraint(), Vacations)
    problem.addConstraint(AllDifferentConstraint(), Animals)
    problem.addConstraint(AllDifferentConstraint(), MusicGenres)

    # Clues:
    # 1. The person who loves beach vacations is Eric.
    problem.addConstraint(lambda beach, eric: beach == eric, ("beach", "Eric"))

    # 2. The person who loves pop music is the person who loves beach vacations.
    problem.addConstraint(lambda pop, beach: pop == beach, ("pop", "beach"))

    # 3. The person who loves rock music is the person who loves mystery books.
    problem.addConstraint(lambda rock, mystery: rock == mystery, ("rock", "mystery"))

    # 4. The cat lover is not in the second house.
    problem.addConstraint(lambda cat: cat != 2, ("cat",))

    # 5. The person who loves mystery books is in the first house.
    problem.addConstraint(lambda mystery: mystery == 1, ("mystery",))

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle.")
    solution = solutions[0]

    # Build output rows in house order
    header = ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"]
    rows = []
    for h in sorted(houses):
        name = next(n for n in Names if solution[n] == h)
        book = next(b for b in BookGenres if solution[b] == h)
        vacation = next(v for v in Vacations if solution[v] == h)
        animal = next(a for a in Animals if solution[a] == h)
        music = next(m for m in MusicGenres if solution[m] == h)
        rows.append([str(h), name, book, vacation, animal, music])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_puzzle()