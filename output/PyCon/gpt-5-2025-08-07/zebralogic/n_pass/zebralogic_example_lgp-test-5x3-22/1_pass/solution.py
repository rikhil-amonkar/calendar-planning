import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]

    names = ["Arnold", "Eric", "Bob", "Peter", "Alice"]
    smoothies = ["desert", "watermelon", "lime", "cherry", "dragonfruit"]
    nationalities = ["german", "swede", "norwegian", "dane", "brit"]

    problem = Problem()

    # Add variables for positions of each attribute
    for n in names:
        problem.addVariable(f"Name-{n}", houses)
    for s in smoothies:
        problem.addVariable(f"Smoothie-{s}", houses)
    for nat in nationalities:
        problem.addVariable(f"Nationality-{nat}", houses)

    # All attributes in each category must be in different houses
    problem.addConstraint(AllDifferentConstraint(), [f"Name-{n}" for n in names])
    problem.addConstraint(AllDifferentConstraint(), [f"Smoothie-{s}" for s in smoothies])
    problem.addConstraint(AllDifferentConstraint(), [f"Nationality-{nat}" for nat in nationalities])

    # Clues:
    # 1. The Dragonfruit smoothie lover is somewhere to the left of Eric.
    problem.addConstraint(lambda d, e: d < e, ["Smoothie-dragonfruit", "Name-Eric"])

    # 2. The Dragonfruit smoothie lover is in the second house.
    problem.addConstraint(lambda d: d == 2, ["Smoothie-dragonfruit"])

    # 3. Peter is not in the first house.
    problem.addConstraint(lambda p: p != 1, ["Name-Peter"])

    # 4. The Dane and the British person are next to each other.
    problem.addConstraint(lambda d, b: abs(d - b) == 1, ["Nationality-dane", "Nationality-brit"])

    # 5. The Desert smoothie lover is not in the fifth house.
    problem.addConstraint(lambda d: d != 5, ["Smoothie-desert"])

    # 6. The Swedish person is somewhere to the left of the Dragonfruit smoothie lover.
    problem.addConstraint(lambda sw, d: sw < d, ["Nationality-swede", "Smoothie-dragonfruit"])

    # 7. There are two houses between the person who drinks Lime smoothies and the Dane.
    problem.addConstraint(lambda l, d: abs(l - d) == 3, ["Smoothie-lime", "Nationality-dane"])

    # 8. Bob is the Dane.
    problem.addConstraint(lambda nb, nd: nb == nd, ["Name-Bob", "Nationality-dane"])

    # 9. Alice is the Norwegian.
    problem.addConstraint(lambda na, nn: na == nn, ["Name-Alice", "Nationality-norwegian"])

    # 10. Alice is in the third house.
    problem.addConstraint(lambda a: a == 3, ["Name-Alice"])

    # 11. The Watermelon smoothie lover is in the third house.
    problem.addConstraint(lambda w: w == 3, ["Smoothie-watermelon"])

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")
    # Expecting a unique solution; pick the first
    sol = solutions[0]

    # Build output rows ordered by house 1..5
    rows = []
    for h in houses:
        # Determine the name at house h
        name_at_h = next(n for n in names if sol[f"Name-{n}"] == h)
        smoothie_at_h = next(s for s in smoothies if sol[f"Smoothie-{s}"] == h)
        nationality_at_h = next(nat for nat in nationalities if sol[f"Nationality-{nat}"] == h)
        rows.append([str(h), name_at_h, smoothie_at_h, nationality_at_h])

    output = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Nationality"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))