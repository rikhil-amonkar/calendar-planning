from z3 import Solver, Int, Distinct, Abs, sat
import json

def solve_puzzle():
    s = Solver()

    # Define integer variables for each Name (houses 1 to 6)
    Arnold = Int('Arnold')
    Eric = Int('Eric')
    Bob = Int('Bob')
    Alice = Int('Alice')
    Carol = Int('Carol')
    Peter = Int('Peter')
    names = [Arnold, Eric, Bob, Alice, Carol, Peter]
    name_labels = ["Arnold", "Eric", "Bob", "Alice", "Carol", "Peter"]

    # Define integer variables for each Mother
    Sarah = Int('Sarah')
    Holly = Int('Holly')
    Janelle = Int('Janelle')
    Aniya = Int('Aniya')
    Penny = Int('Penny')
    Kailyn = Int('Kailyn')
    mothers = [Sarah, Holly, Janelle, Aniya, Penny, Kailyn]
    mother_labels = ["Sarah", "Holly", "Janelle", "Aniya", "Penny", "Kailyn"]

    # Define integer variables for each Pet
    hamster = Int('hamster')
    dog = Int('dog')
    bird = Int('bird')
    cat = Int('cat')
    fish = Int('fish')
    rabbit = Int('rabbit')
    pets = [hamster, dog, bird, cat, fish, rabbit]
    pet_labels = ["hamster", "dog", "bird", "cat", "fish", "rabbit"]

    # Each variable must be in the domain 1 through 6 (houses)
    all_vars = names + mothers + pets
    for var in all_vars:
        s.add(var >= 1, var <= 6)

    # All items within each category must be in different houses.
    s.add(Distinct(names))
    s.add(Distinct(mothers))
    s.add(Distinct(pets))

    # Puzzle Constraints:
    # 1. Bob is not in the second house.
    s.add(Bob != 2)

    # 2. There are two houses between the person who has a cat and the person who owns a rabbit.
    s.add(Abs(cat - rabbit) == 3)

    # 3. The person who has a cat is directly left of the person whose mother's name is Holly.
    s.add(cat + 1 == Holly)

    # 4. The person with a pet hamster is directly left of the person who owns a rabbit.
    s.add(hamster + 1 == rabbit)

    # 5. The person who owns a rabbit is Eric.
    s.add(rabbit == Eric)

    # 6. There is one house between the person who owns a dog and the person who has a cat.
    s.add(Abs(dog - cat) == 2)

    # 7. The person who has a cat is the person whose mother's name is Janelle.
    s.add(cat == Janelle)

    # 8. Alice is directly left of Carol.
    s.add(Alice + 1 == Carol)

    # 9. Carol is the person whose mother's name is Aniya.
    s.add(Carol == Aniya)

    # 10. Arnold is the person who has a cat.
    s.add(Arnold == cat)

    # 11. The person whose mother's name is Kailyn is the person who owns a rabbit.
    s.add(Kailyn == rabbit)

    # 12. The person with an aquarium of fish is the person whose mother's name is Sarah.
    s.add(fish == Sarah)

    # Solve the puzzle.
    if s.check() == sat:
        m = s.model()

        # Build a dictionary for each house number with its associated attributes.
        houses = {i: {"Name": None, "Mother": None, "Pet": None} for i in range(1, 7)}

        # Assign Name values based on the model.
        for label, var in zip(name_labels, names):
            house_num = m.evaluate(var).as_long()
            houses[house_num]["Name"] = label

        # Assign Mother values based on the model.
        for label, var in zip(mother_labels, mothers):
            house_num = m.evaluate(var).as_long()
            houses[house_num]["Mother"] = label

        # Assign Pet values based on the model.
        for label, var in zip(pet_labels, pets):
            house_num = m.evaluate(var).as_long()
            houses[house_num]["Pet"] = label

        # Prepare rows in house order 1 to 6.
        rows = []
        for i in range(1, 7):
            row = [str(i), houses[i]["Name"], houses[i]["Mother"], houses[i]["Pet"]]
            rows.append(row)

        solution = {
            "solution": {
                "header": ["House", "Name", "Mother", "Pet"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": "unsat"}))

if __name__ == "__main__":
    solve_puzzle()