import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = [1, 2, 3, 4, 5]

    names = ["Arnold", "Peter", "Eric", "Alice", "Bob"]
    hobbies = ["painting", "cooking", "knitting", "gardening", "photography"]
    heights = ["very tall", "tall", "very short", "average", "short"]
    foods = ["stew", "grilled cheese", "stir fry", "spaghetti", "pizza"]

    problem = Problem()

    # Add variables for each category with domain 1..5
    problem.addVariables(names, houses)
    problem.addVariables(hobbies, houses)
    problem.addVariables(heights, houses)
    problem.addVariables(foods, houses)

    # All-different constraints within each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), hobbies)
    problem.addConstraint(AllDifferentConstraint(), heights)
    problem.addConstraint(AllDifferentConstraint(), foods)

    # Clues as constraints

    # 1. Bob is the photography enthusiast.
    problem.addConstraint(lambda bob, photo: bob == photo, ("Bob", "photography"))

    # 2. The person who loves eating grilled cheese is the person who is tall.
    problem.addConstraint(lambda gc, t: gc == t, ("grilled cheese", "tall"))

    # 3. Peter is not in the second house.
    problem.addConstraint(lambda p: p != 2, ("Peter",))

    # 4. The person who is tall is directly left of the person who loves stir fry.
    problem.addConstraint(lambda t, sf: t + 1 == sf, ("tall", "stir fry"))

    # 5. The person who loves cooking is the person who has an average height.
    problem.addConstraint(lambda c, a: c == a, ("cooking", "average"))

    # 6. Alice is directly left of the person who is a pizza lover.
    problem.addConstraint(lambda a, pz: a + 1 == pz, ("Alice", "pizza"))

    # 7. The spaghetti eater is not in the second house.
    problem.addConstraint(lambda sp: sp != 2, ("spaghetti",))

    # 8. Eric is not in the fifth house.
    problem.addConstraint(lambda e: e != 5, ("Eric",))

    # 9. The person who is short is Peter.
    problem.addConstraint(lambda s, p: s == p, ("short", "Peter"))

    # 10. The person who has an average height and the person who enjoys gardening are next to each other.
    problem.addConstraint(lambda a, g: abs(a - g) == 1, ("average", "gardening"))

    # 11. The person who paints as a hobby is directly left of the person who loves eating grilled cheese.
    problem.addConstraint(lambda pa, gc: pa + 1 == gc, ("painting", "grilled cheese"))

    # 12. The person who is very short is in the fifth house.
    problem.addConstraint(lambda vs: vs == 5, ("very short",))

    # 13. The person who is tall is in the third house.
    problem.addConstraint(lambda t: t == 3, ("tall",))

    # 14. Alice is somewhere to the right of the photography enthusiast.
    problem.addConstraint(lambda a, ph: a > ph, ("Alice", "photography"))

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found for the given puzzle constraints.")

    sol = solutions[0]

    # Build output rows by house number
    rows = []
    for h in houses:
        name = next(n for n in names if sol[n] == h)
        hobby = next(o for o in hobbies if sol[o] == h)
        height = next(ht for ht in heights if sol[ht] == h)
        food = next(f for f in foods if sol[f] == h)
        rows.append([str(h), name, hobby, height, food])

    output = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Height", "Food"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()