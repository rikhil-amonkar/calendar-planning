import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = range(1, 7)

    names = ["Arnold", "Peter", "Carol", "Alice", "Bob", "Eric"]
    children = ["Alice", "Timothy", "Bella", "Meredith", "Fred", "Samantha"]
    smoothies = ["desert", "cherry", "watermelon", "blueberry", "lime", "dragonfruit"]

    # Helper to namespace variables
    def N(x): return f"N_{x}"
    def C(x): return f"C_{x}"
    def S(x): return f"S_{x}"

    problem = Problem()

    # Add variables for each category with domains 1..6
    for n in names:
        problem.addVariable(N(n), houses)
    for c in children:
        problem.addVariable(C(c), houses)
    for s in smoothies:
        problem.addVariable(S(s), houses)

    # AllDifferent within each category
    problem.addConstraint(AllDifferentConstraint(), [N(n) for n in names])
    problem.addConstraint(AllDifferentConstraint(), [C(c) for c in children])
    problem.addConstraint(AllDifferentConstraint(), [S(s) for s in smoothies])

    # Clues as constraints
    # 1. Fred child and Desert smoothie are next to each other.
    problem.addConstraint(lambda cf, sd: abs(cf - sd) == 1, (C("Fred"), S("desert")))

    # 2. Blueberry left of Fred child.
    problem.addConstraint(lambda sb, cf: sb < cf, (S("blueberry"), C("Fred")))

    # 3. Alice is not in the fifth house.
    problem.addConstraint(lambda x: x != 5, (N("Alice"),))

    # 4. Samantha child not in the second house.
    problem.addConstraint(lambda x: x != 2, (C("Samantha"),))

    # 5. Watermelon to the right of Cherry.
    problem.addConstraint(lambda sw, sc: sw > sc, (S("watermelon"), S("cherry")))

    # 6. Alice is the mother of child Alice.
    problem.addConstraint(lambda na, ca: na == ca, (N("Alice"), C("Alice")))

    # 7. Alice is the Watermelon smoothie lover.
    problem.addConstraint(lambda na, sw: na == sw, (N("Alice"), S("watermelon")))

    # 8. Peter is somewhere to the right of child Samantha.
    problem.addConstraint(lambda np, cs: np > cs, (N("Peter"), C("Samantha")))

    # 9. Arnold is not in the second house.
    problem.addConstraint(lambda x: x != 2, (N("Arnold"),))

    # 10. Bob is the mother of Timothy.
    problem.addConstraint(lambda nb, ct: nb == ct, (N("Bob"), C("Timothy")))

    # 11. Arnold is directly left of Carol.
    problem.addConstraint(lambda na, nc: na + 1 == nc, (N("Arnold"), N("Carol")))

    # 12. Cherry directly left of Samantha (child).
    problem.addConstraint(lambda sc, cs: sc + 1 == cs, (S("cherry"), C("Samantha")))

    # 13. Meredith (child) is in the sixth house.
    problem.addConstraint(lambda x: x == 6, (C("Meredith"),))

    # 14. Dragonfruit smoothie lover is the mother of Meredith.
    problem.addConstraint(lambda sd, cm: sd == cm, (S("dragonfruit"), C("Meredith")))

    solutions = problem.getSolutions()

    if not solutions:
        raise RuntimeError("No solution found for the puzzle.")

    # Assuming unique solution; take the first
    sol = solutions[0]

    # Build inverse mappings from position to attribute
    name_at = {sol[N(n)]: n for n in names}
    child_at = {sol[C(c)]: c for c in children}
    smoothie_at = {sol[S(s)]: s for s in smoothies}

    output = {
        "solution": {
            "header": ["House", "Name", "Children", "Smoothie"],
            "rows": []
        }
    }

    for h in range(1, 7):
        output["solution"]["rows"].append([
            str(h),
            name_at[h],
            child_at[h],
            smoothie_at[h],
        ])

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()