import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = [1, 2, 3, 4, 5]

    # Attributes
    names = ["Alice", "Bob", "Arnold", "Eric", "Peter"]
    vacations = ["cruise", "city", "camping", "beach", "mountain"]
    children = ["Bella", "Samantha", "Fred", "Meredith", "Timothy"]
    nationalities = ["dane", "norwegian", "brit", "german", "swede"]

    problem = Problem()

    # Add variables with domains (house numbers 1..5)
    problem.addVariables(names, houses)
    problem.addVariables(vacations, houses)
    problem.addVariables(children, houses)
    problem.addVariables(nationalities, houses)

    # AllDifferent constraints within each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), vacations)
    problem.addConstraint(AllDifferentConstraint(), children)
    problem.addConstraint(AllDifferentConstraint(), nationalities)

    # Clues as constraints:

    # 1. The Norwegian is Peter.
    problem.addConstraint(lambda peter, norwegian: peter == norwegian, ("Peter", "norwegian"))

    # 2. The Swedish person's child is named Bella.
    problem.addConstraint(lambda swede, bella: swede == bella, ("swede", "Bella"))

    # 3. The person who loves beach vacations is directly left of the person's child named Samantha.
    problem.addConstraint(lambda beach, samantha: beach == samantha - 1, ("beach", "Samantha"))

    # 4. Bella is not in the second house.
    problem.addConstraint(lambda bella: bella != 2, ("Bella",))

    # 5. Alice is the British person.
    problem.addConstraint(lambda alice, brit: alice == brit, ("Alice", "brit"))

    # 6. The person who likes going on cruises is in the first house.
    problem.addConstraint(lambda cruise: cruise == 1, ("cruise",))

    # 7. Meredith is in the fourth house.
    problem.addConstraint(lambda meredith: meredith == 4, ("Meredith",))

    # 8. Eric is not in the fifth house.
    problem.addConstraint(lambda eric: eric != 5, ("Eric",))

    # 9. The Swedish person is somewhere to the right of the Norwegian.
    problem.addConstraint(lambda swede, norwegian: swede > norwegian, ("swede", "norwegian"))

    # 10. There is one house between Fred and the city.
    problem.addConstraint(lambda fred, city: abs(fred - city) == 2, ("Fred", "city"))

    # 11. Bob is the person who enjoys camping trips.
    problem.addConstraint(lambda bob, camping: bob == camping, ("Bob", "camping"))

    # 12. The Dane is in the fifth house.
    problem.addConstraint(lambda dane: dane == 5, ("dane",))

    # 13. Camping is not in the fifth house.
    problem.addConstraint(lambda camping: camping != 5, ("camping",))

    solutions = problem.getSolutions()

    if not solutions:
        output = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Children", "Nationality"],
                "rows": []
            }
        }
        print(json.dumps(output))
        return

    sol = solutions[0]

    rows = []
    for h in houses:
        name = next(n for n in names if sol[n] == h)
        vacation = next(v for v in vacations if sol[v] == h)
        child = next(c for c in children if sol[c] == h)
        nationality = next(nat for nat in nationalities if sol[nat] == h)
        rows.append([str(h), name, vacation, child, nationality])

    output = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Children", "Nationality"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()