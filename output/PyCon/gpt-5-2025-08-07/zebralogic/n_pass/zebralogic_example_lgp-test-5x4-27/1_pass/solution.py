import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = [1, 2, 3, 4, 5]

    names = ["Peter", "Alice", "Eric", "Bob", "Arnold"]
    birthdays = ["april", "feb", "mar", "jan", "sept"]
    cigars = ["pall mall", "prince", "dunhill", "blends", "blue master"]
    drinks = ["water", "coffee", "tea", "milk", "root beer"]

    # Create the problem
    problem = Problem()

    # Create variables: each attribute value maps to a house number
    for n in names:
        problem.addVariable(("Name", n), houses)
    for b in birthdays:
        problem.addVariable(("Birthday", b), houses)
    for c in cigars:
        problem.addVariable(("Cigar", c), houses)
    for d in drinks:
        problem.addVariable(("Drink", d), houses)

    # All different within each attribute set
    problem.addConstraint(AllDifferentConstraint(), [("Name", n) for n in names])
    problem.addConstraint(AllDifferentConstraint(), [("Birthday", b) for b in birthdays])
    problem.addConstraint(AllDifferentConstraint(), [("Cigar", c) for c in cigars])
    problem.addConstraint(AllDifferentConstraint(), [("Drink", d) for d in drinks])

    # Clues:
    # 1. The root beer lover is Eric.
    problem.addConstraint(lambda rb, eric: rb == eric, [("Drink", "root beer"), ("Name", "Eric")])

    # 2. The person partial to Pall Mall is in the third house.
    problem.addConstraint(lambda x: x == 3, [("Cigar", "pall mall")])

    # 3. The person whose birthday is in April is Bob.
    problem.addConstraint(lambda apr, bob: apr == bob, [("Birthday", "april"), ("Name", "Bob")])

    # 4. The Dunhill smoker is the person whose birthday is in March.
    problem.addConstraint(lambda dun, mar: dun == mar, [("Cigar", "dunhill"), ("Birthday", "mar")])

    # 5. Peter is somewhere to the right of the root beer lover.
    problem.addConstraint(lambda peter, rb: peter > rb, [("Name", "Peter"), ("Drink", "root beer")])

    # 6. There is one house between the person whose birthday is in January and Peter.
    problem.addConstraint(lambda jan, peter: abs(jan - peter) == 2, [("Birthday", "jan"), ("Name", "Peter")])

    # 7. The person who smokes many unique blends is the person whose birthday is in February.
    problem.addConstraint(lambda blends, feb: blends == feb, [("Cigar", "blends"), ("Birthday", "feb")])

    # 8. The person whose birthday is in February is in the second house.
    problem.addConstraint(lambda feb: feb == 2, [("Birthday", "feb")])

    # 9. Arnold is directly left of Peter.
    problem.addConstraint(lambda arnold, peter: arnold + 1 == peter, [("Name", "Arnold"), ("Name", "Peter")])

    # 10. The person who likes milk is not in the fifth house.
    problem.addConstraint(lambda milk: milk != 5, [("Drink", "milk")])

    # 11. The person who smokes Blue Master is the coffee drinker.
    problem.addConstraint(lambda blue, coffee: blue == coffee, [("Cigar", "blue master"), ("Drink", "coffee")])

    # 12. There is one house between the tea drinker and the coffee drinker.
    problem.addConstraint(lambda tea, coffee: abs(tea - coffee) == 2, [("Drink", "tea"), ("Drink", "coffee")])

    # 13. Eric is in the third house.
    problem.addConstraint(lambda eric: eric == 3, [("Name", "Eric")])

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found for the given puzzle.")

    sol = solutions[0]

    # Invert mappings: for each house, find the value for each attribute group
    house_to_name = {}
    for n in names:
        house_to_name[sol[("Name", n)]] = n

    house_to_birthday = {}
    for b in birthdays:
        house_to_birthday[sol[("Birthday", b)]] = b

    house_to_cigar = {}
    for c in cigars:
        house_to_cigar[sol[("Cigar", c)]] = c

    house_to_drink = {}
    for d in drinks:
        house_to_drink[sol[("Drink", d)]] = d

    output = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
            "rows": []
        }
    }

    for h in houses:
        row = [
            str(h),
            house_to_name[h],
            house_to_birthday[h],
            house_to_cigar[h],
            house_to_drink[h]
        ]
        output["solution"]["rows"].append(row)

    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()