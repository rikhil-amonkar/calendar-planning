import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    # Define attributes
    houses = [1, 2, 3, 4]
    names = ["Alice", "Peter", "Arnold", "Eric"]
    cigars = ["prince", "dunhill", "blue master", "pall mall"]
    sports = ["swimming", "basketball", "soccer", "tennis"]
    drinks = ["coffee", "water", "milk", "tea"]

    # Create problem
    problem = Problem()

    # Add variables for each attribute value mapped to house positions
    for var in names + cigars + sports + drinks:
        problem.addVariable(var, houses)

    # Uniqueness within each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), cigars)
    problem.addConstraint(AllDifferentConstraint(), sports)
    problem.addConstraint(AllDifferentConstraint(), drinks)

    # Apply clues as constraints

    # 1. Peter is in the fourth house.
    problem.addConstraint(lambda p: p == 4, ("Peter",))

    # 2. The tea drinker is the person who loves basketball.
    problem.addConstraint(lambda t, b: t == b, ("tea", "basketball"))

    # 3. Arnold is the person who smokes Blue Master.
    problem.addConstraint(lambda a, bm: a == bm, ("Arnold", "blue master"))

    # 4. The person who loves basketball is Eric.
    problem.addConstraint(lambda b, e: b == e, ("basketball", "Eric"))

    # 5. The person who loves tennis is the person who smokes Blue Master.
    problem.addConstraint(lambda t, bm: t == bm, ("tennis", "blue master"))

    # 6. There are two houses between the one who only drinks water and Peter.
    problem.addConstraint(lambda w, p: abs(w - p) == 3, ("water", "Peter"))

    # 7. The coffee drinker is Arnold.
    problem.addConstraint(lambda c, a: c == a, ("coffee", "Arnold"))

    # 8. The person who loves basketball is in the third house.
    problem.addConstraint(lambda b: b == 3, ("basketball",))

    # 9. The Prince smoker is the person who loves soccer.
    problem.addConstraint(lambda pr, s: pr == s, ("prince", "soccer"))

    # 10. Peter is the person partial to Pall Mall.
    problem.addConstraint(lambda p, pm: p == pm, ("Peter", "pall mall"))

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the puzzle.")

    sol = solutions[0]

    # Build output rows ordered by house 1..4
    rows = []
    for h in houses:
        name = next(n for n in names if sol[n] == h)
        cigar = next(c for c in cigars if sol[c] == h)
        sport = next(s for s in sports if sol[s] == h)
        drink = next(d for d in drinks if sol[d] == h)
        rows.append([str(h), name, cigar, sport, drink])

    result = {
        "solution": {
            "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, separators=(",", ":")))