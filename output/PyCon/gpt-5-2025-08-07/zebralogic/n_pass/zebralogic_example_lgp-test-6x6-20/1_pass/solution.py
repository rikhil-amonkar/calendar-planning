import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = range(1, 7)

    Names = ["Alice", "Peter", "Eric", "Bob", "Arnold", "Carol"]
    Cigars = ["pall mall", "yellow monster", "dunhill", "blue master", "prince", "blends"]
    Music = ["hip hop", "jazz", "country", "pop", "classical", "rock"]
    Drinks = ["water", "milk", "boba tea", "tea", "root beer", "coffee"]
    Mothers = ["Kailyn", "Penny", "Janelle", "Holly", "Sarah", "Aniya"]
    Food = ["soup", "pizza", "spaghetti", "stir fry", "stew", "grilled cheese"]

    problem = Problem()

    # Create variables for each attribute value representing the house index (1..6)
    var_names = {}

    for n in Names:
        var_names[("Name", n)] = f"Name_{n}"
        problem.addVariable(var_names[("Name", n)], houses)
    for c in Cigars:
        var_names[("Cigar", c)] = f"Cigar_{c}"
        problem.addVariable(var_names[("Cigar", c)], houses)
    for m in Music:
        var_names[("Music", m)] = f"Music_{m}"
        problem.addVariable(var_names[("Music", m)], houses)
    for d in Drinks:
        var_names[("Drink", d)] = f"Drink_{d}"
        problem.addVariable(var_names[("Drink", d)], houses)
    for mo in Mothers:
        var_names[("Mother", mo)] = f"Mother_{mo}"
        problem.addVariable(var_names[("Mother", mo)], houses)
    for f in Food:
        var_names[("Food", f)] = f"Food_{f}"
        problem.addVariable(var_names[("Food", f)], houses)

    # AllDifferent constraints for each category
    problem.addConstraint(AllDifferentConstraint(), [var_names[("Name", n)] for n in Names])
    problem.addConstraint(AllDifferentConstraint(), [var_names[("Cigar", c)] for c in Cigars])
    problem.addConstraint(AllDifferentConstraint(), [var_names[("Music", m)] for m in Music])
    problem.addConstraint(AllDifferentConstraint(), [var_names[("Drink", d)] for d in Drinks])
    problem.addConstraint(AllDifferentConstraint(), [var_names[("Mother", mo)] for mo in Mothers])
    problem.addConstraint(AllDifferentConstraint(), [var_names[("Food", f)] for f in Food])

    # Helper functions for constraints
    def eq(a, b):
        return a == b

    def ne(a, b):
        return a != b

    def left_of(a, b):
        return a < b

    def right_of(a, b):
        return a > b

    def directly_left_of(a, b):
        return a + 1 == b

    def distance(a, b, d):
        return abs(a - b) == d

    # Constraints from clues

    # 1. Carol is directly left of the person who loves eating grilled cheese.
    problem.addConstraint(lambda carol, grilled: directly_left_of(carol, grilled),
                          (var_names[("Name", "Carol")], var_names[("Food", "grilled cheese")]))

    # 2. Eric is not in the second house.
    problem.addConstraint(lambda eric: eric != 2, (var_names[("Name", "Eric")],))

    # 3. Holly is somewhere to the right of Carol.
    problem.addConstraint(lambda holly, carol: right_of(holly, carol),
                          (var_names[("Mother", "Holly")], var_names[("Name", "Carol")]))

    # 4. Grilled cheese is to the right of rock.
    problem.addConstraint(lambda grilled, rock: right_of(grilled, rock),
                          (var_names[("Food", "grilled cheese")], var_names[("Music", "rock")]))

    # 5. Eric is directly left of Carol.
    problem.addConstraint(lambda eric, carol: directly_left_of(eric, carol),
                          (var_names[("Name", "Eric")], var_names[("Name", "Carol")]))

    # 6. Pop is not in the third house.
    problem.addConstraint(lambda pop: pop != 3, (var_names[("Music", "pop")],))

    # 7. Eric loves country music.
    problem.addConstraint(eq, (var_names[("Name", "Eric")], var_names[("Music", "country")]))

    # 8. Classical is in the sixth house.
    problem.addConstraint(lambda classical: classical == 6, (var_names[("Music", "classical")],))

    # 9. Coffee drinker is Bob.
    problem.addConstraint(eq, (var_names[("Drink", "coffee")], var_names[("Name", "Bob")]))

    # 10. Blends is Peter.
    problem.addConstraint(eq, (var_names[("Cigar", "blends")], var_names[("Name", "Peter")]))

    # 11. Stew is not in the fifth house.
    problem.addConstraint(lambda stew: stew != 5, (var_names[("Food", "stew")],))

    # 12. Root beer is directly left of Janelle.
    problem.addConstraint(lambda rootbeer, janelle: directly_left_of(rootbeer, janelle),
                          (var_names[("Drink", "root beer")], var_names[("Mother", "Janelle")]))

    # 13. Two houses between Sarah and Yellow Monster.
    problem.addConstraint(lambda sarah, yellow: distance(sarah, yellow, 3),
                          (var_names[("Mother", "Sarah")], var_names[("Cigar", "yellow monster")]))

    # 14. Eric is the tea drinker.
    problem.addConstraint(eq, (var_names[("Name", "Eric")], var_names[("Drink", "tea")]))

    # 15. Pall Mall to the right of Stir Fry.
    problem.addConstraint(lambda pallmall, stirfry: right_of(pallmall, stirfry),
                          (var_names[("Cigar", "pall mall")], var_names[("Food", "stir fry")]))

    # 16. Soup is Bob.
    problem.addConstraint(eq, (var_names[("Food", "soup")], var_names[("Name", "Bob")]))

    # 17. Hip hop directly left of Kailyn.
    problem.addConstraint(lambda hiphop, kailyn: directly_left_of(hiphop, kailyn),
                          (var_names[("Music", "hip hop")], var_names[("Mother", "Kailyn")]))

    # 18. Arnold is to the right of Kailyn.
    problem.addConstraint(lambda arnold, kailyn: right_of(arnold, kailyn),
                          (var_names[("Name", "Arnold")], var_names[("Mother", "Kailyn")]))

    # 19. Water directly left of Blue Master.
    problem.addConstraint(lambda water, bluemaster: directly_left_of(water, bluemaster),
                          (var_names[("Drink", "water")], var_names[("Cigar", "blue master")]))

    # 20. Spaghetti is to the left of Blends. (interpreting the intended meaning)
    problem.addConstraint(lambda spaghetti, blends: left_of(spaghetti, blends),
                          (var_names[("Food", "spaghetti")], var_names[("Cigar", "blends")]))

    # 21. Sarah directly left of Jazz.
    problem.addConstraint(lambda sarah, jazz: directly_left_of(sarah, jazz),
                          (var_names[("Mother", "Sarah")], var_names[("Music", "jazz")]))

    # 22. Hip hop directly left of Root Beer.
    problem.addConstraint(lambda hiphop, rootbeer: directly_left_of(hiphop, rootbeer),
                          (var_names[("Music", "hip hop")], var_names[("Drink", "root beer")]))

    # 23. Water equals Stew.
    problem.addConstraint(eq, (var_names[("Drink", "water")], var_names[("Food", "stew")]))

    # 24. Dunhill not in second house.
    problem.addConstraint(lambda dunhill: dunhill != 2, (var_names[("Cigar", "dunhill")],))

    # 25. Milk is Janelle.
    problem.addConstraint(eq, (var_names[("Drink", "milk")], var_names[("Mother", "Janelle")]))

    # 26. Eric is Aniya.
    problem.addConstraint(eq, (var_names[("Name", "Eric")], var_names[("Mother", "Aniya")]))

    solutions = problem.getSolutions()

    if not solutions:
        output = {
            "solution": {
                "header": ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"],
                "rows": []
            }
        }
        print(json.dumps(output))
        return

    sol = solutions[0]

    # Build output rows per house 1..6
    header = ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"]
    rows = []
    for h in range(1, 7):
        name_val = next(n for n in Names if sol[var_names[("Name", n)]] == h)
        cigar_val = next(c for c in Cigars if sol[var_names[("Cigar", c)]] == h)
        music_val = next(m for m in Music if sol[var_names[("Music", m)]] == h)
        drink_val = next(d for d in Drinks if sol[var_names[("Drink", d)]] == h)
        mother_val = next(mo for mo in Mothers if sol[var_names[("Mother", mo)]] == h)
        food_val = next(f for f in Food if sol[var_names[("Food", f)]] == h)
        rows.append([str(h), name_val, cigar_val, music_val, drink_val, mother_val, food_val])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()