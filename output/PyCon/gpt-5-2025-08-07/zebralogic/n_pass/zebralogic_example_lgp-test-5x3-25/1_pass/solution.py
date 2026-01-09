import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define houses and attributes
    houses = range(1, 6)

    names = ["Arnold", "Bob", "Alice", "Eric", "Peter"]
    heights = ["very tall", "average", "tall", "very short", "short"]
    foods = ["stew", "grilled cheese", "spaghetti", "pizza", "stir fry"]

    # Set up the problem
    problem = Problem()

    # Add variables: each attribute maps to a house number 1..5
    problem.addVariables(names, houses)
    problem.addVariables(heights, houses)
    problem.addVariables(foods, houses)

    # Each category has unique positions
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), heights)
    problem.addConstraint(AllDifferentConstraint(), foods)

    # Clues as constraints
    # 1. Alice is the person who is short.
    problem.addConstraint(lambda a, s: a == s, ("Alice", "short"))

    # 2. The person who is tall is in the third house.
    problem.addConstraint(lambda t: t == 3, ("tall",))

    # 3. The person who has an average height is not in the second house.
    problem.addConstraint(lambda a: a != 2, ("average",))

    # 4. The person who has an average height is somewhere to the left of the person who loves the stew.
    problem.addConstraint(lambda a, st: a < st, ("average", "stew"))

    # 5. The person who loves stir fry is Arnold.
    problem.addConstraint(lambda sf, ar: sf == ar, ("stir fry", "Arnold"))

    # 6. The person who is a pizza lover is the person who is tall.
    problem.addConstraint(lambda p, t: p == t, ("pizza", "tall"))

    # 7. Eric is the person who is tall.
    problem.addConstraint(lambda e, t: e == t, ("Eric", "tall"))

    # 8. Bob is somewhere to the right of Arnold.
    problem.addConstraint(lambda b, ar: b > ar, ("Bob", "Arnold"))

    # 9. The person who loves eating grilled cheese is somewhere to the right of Eric.
    problem.addConstraint(lambda gc, e: gc > e, ("grilled cheese", "Eric"))

    # 10. The person who is very short is somewhere to the left of Arnold.
    problem.addConstraint(lambda vs, ar: vs < ar, ("very short", "Arnold"))

    solutions = problem.getSolutions()
    if not solutions:
        print(json.dumps({"solution": {"header": ["House", "Name", "Height", "Food"], "rows": []}}))
        return

    sol = solutions[0]

    # Invert mappings for output: house -> attribute
    inv_names = {sol[name]: name for name in names}
    inv_heights = {sol[h]: h for h in heights}
    inv_foods = {sol[f]: f for f in foods}

    rows = []
    for h in range(1, 6):
        row = [str(h), inv_names[h], inv_heights[h], inv_foods[h]]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "Height", "Food"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()