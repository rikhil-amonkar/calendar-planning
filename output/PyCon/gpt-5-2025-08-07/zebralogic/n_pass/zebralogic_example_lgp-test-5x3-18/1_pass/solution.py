import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]

    names = ["Alice", "Eric", "Arnold", "Bob", "Peter"]
    flowers = ["tulips", "roses", "lilies", "daffodils", "carnations"]
    animals = ["dog", "horse", "cat", "bird", "fish"]

    problem = Problem()

    # Add variables for each attribute with domain 1..5 (house positions)
    for n in names:
        problem.addVariable(n, houses)
    for f in flowers:
        problem.addVariable(f, houses)
    for a in animals:
        problem.addVariable(a, houses)

    # Uniqueness constraints within each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), flowers)
    problem.addConstraint(AllDifferentConstraint(), animals)

    # Clues:
    # 1. Alice is in the second house.
    problem.addConstraint(lambda x: x == 2, ("Alice",))

    # 2. The person who loves the boquet of lilies is the bird keeper.
    problem.addConstraint(lambda l, b: l == b, ("lilies", "bird"))

    # 3. Peter is somewhere to the right of the person who loves the vase of tulips.
    problem.addConstraint(lambda p, t: p > t, ("Peter", "tulips"))

    # 4. The fish enthusiast is the person who loves a bouquet of daffodils.
    problem.addConstraint(lambda fi, d: fi == d, ("fish", "daffodils"))

    # 5. The person who keeps horses is Eric.
    problem.addConstraint(lambda h, e: h == e, ("horse", "Eric"))

    # 6. There are two houses between the dog owner and Bob. (difference of 3)
    problem.addConstraint(lambda dog, bob: abs(dog - bob) == 3, ("dog", "Bob"))

    # 7. The fish enthusiast is directly left of Bob.
    problem.addConstraint(lambda fi, bob: fi + 1 == bob, ("fish", "Bob"))

    # 8. Alice is directly left of the person who keeps horses.
    problem.addConstraint(lambda a, h: a + 1 == h, ("Alice", "horse"))

    # 9. The person who loves a carnations arrangement is directly left of the person who loves the vase of tulips.
    problem.addConstraint(lambda c, t: c + 1 == t, ("carnations", "tulips"))

    # 10. The cat lover is not in the first house.
    problem.addConstraint(lambda c: c != 1, ("cat",))

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle.")

    # Expect a unique solution; take the first if multiple
    sol = solutions[0]

    # Build rows per house
    rows = []
    for h in houses:
        # Find the name, flower, animal at house h
        name_at_h = next(n for n in names if sol[n] == h)
        flower_at_h = next(f for f in flowers if sol[f] == h)
        animal_at_h = next(a for a in animals if sol[a] == h)
        rows.append([str(h), name_at_h, flower_at_h, animal_at_h])

    result = {
        "solution": {
            "header": ["House", "Name", "Flower", "Animal"],
            "rows": rows
        }
    }

    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))