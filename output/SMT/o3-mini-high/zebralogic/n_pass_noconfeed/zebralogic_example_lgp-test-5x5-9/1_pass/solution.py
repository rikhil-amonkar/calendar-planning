from z3 import *
import json

def main():
    s = Solver()
    n = 5

    # Create Z3 integer variables for each attribute for each house (houses are 0-indexed, representing House 1-5)
    name_vars = [Int(f"name_{i}") for i in range(n)]
    drink_vars = [Int(f"drink_{i}") for i in range(n)]
    color_vars = [Int(f"color_{i}") for i in range(n)]
    flower_vars = [Int(f"flower_{i}") for i in range(n)]
    hobby_vars = [Int(f"hobby_{i}") for i in range(n)]

    # Define domains for each variable (0 to 4)
    for i in range(n):
        s.add(And(name_vars[i] >= 0, name_vars[i] < n))
        s.add(And(drink_vars[i] >= 0, drink_vars[i] < n))
        s.add(And(color_vars[i] >= 0, color_vars[i] < n))
        s.add(And(flower_vars[i] >= 0, flower_vars[i] < n))
        s.add(And(hobby_vars[i] >= 0, hobby_vars[i] < n))

    # All attributes must be distinct across houses
    s.add(Distinct(name_vars))
    s.add(Distinct(drink_vars))
    s.add(Distinct(color_vars))
    s.add(Distinct(flower_vars))
    s.add(Distinct(hobby_vars))

    # Mapping for each attribute category
    names = ["Bob", "Arnold", "Peter", "Alice", "Eric"]
    drinks = ["milk", "root beer", "coffee", "tea", "water"]
    colors = ["blue", "green", "white", "yellow", "red"]
    flowers = ["daffodils", "roses", "lilies", "tulips", "carnations"]
    hobbies = ["painting", "cooking", "photography", "gardening", "knitting"]

    # Clue 1: Alice is not in the fourth house.
    # House 4 -> index 3 must not be Alice (Alice is index 3 in names)
    s.add(name_vars[3] != names.index("Alice"))

    # Clue 2: The root beer lover is the person who enjoys gardening.
    for i in range(n):
        s.add(Implies(drink_vars[i] == drinks.index("root beer"), hobby_vars[i] == hobbies.index("gardening")))
        s.add(Implies(hobby_vars[i] == hobbies.index("gardening"), drink_vars[i] == drinks.index("root beer")))

    # Clue 3: The person whose favorite color is green is the coffee drinker.
    for i in range(n):
        s.add(Implies(color_vars[i] == colors.index("green"), drink_vars[i] == drinks.index("coffee")))
        s.add(Implies(drink_vars[i] == drinks.index("coffee"), color_vars[i] == colors.index("green")))

    # Clue 4: The person whose favorite color is green is the person who loves the bouquet of lilies.
    for i in range(n):
        s.add(Implies(color_vars[i] == colors.index("green"), flower_vars[i] == flowers.index("lilies")))
        s.add(Implies(flower_vars[i] == flowers.index("lilies"), color_vars[i] == colors.index("green")))

    # Clue 5: The person who loves blue is somewhere to the right of the person who loves a bouquet of daffodils.
    for i in range(n):
        for j in range(n):
            s.add(Implies(And(color_vars[i] == colors.index("blue"), flower_vars[j] == flowers.index("daffodils")), i > j))

    # Clue 6: The person who loves cooking is the person who loves blue.
    for i in range(n):
        s.add(Implies(hobby_vars[i] == hobbies.index("cooking"), color_vars[i] == colors.index("blue")))
        s.add(Implies(color_vars[i] == colors.index("blue"), hobby_vars[i] == hobbies.index("cooking")))

    # Clue 7: Eric is directly left of the tea drinker.
    for i in range(n - 1):
        s.add(Implies(name_vars[i] == names.index("Eric"), drink_vars[i + 1] == drinks.index("tea")))
    # Eric cannot be in the last house.
    s.add(name_vars[n - 1] != names.index("Eric"))

    # Clue 8: The one who only drinks water is Peter.
    for i in range(n):
        s.add(Implies(drink_vars[i] == drinks.index("water"), name_vars[i] == names.index("Peter")))
        s.add(Implies(name_vars[i] == names.index("Peter"), drink_vars[i] == drinks.index("water")))

    # Clue 9: Arnold is the photography enthusiast.
    for i in range(n):
        s.add(Implies(name_vars[i] == names.index("Arnold"), hobby_vars[i] == hobbies.index("photography")))
        s.add(Implies(hobby_vars[i] == hobbies.index("photography"), name_vars[i] == names.index("Arnold")))

    # Clue 10: The person who loves white is the person who loves the rose bouquet.
    for i in range(n):
        s.add(Implies(color_vars[i] == colors.index("white"), flower_vars[i] == flowers.index("roses")))
        s.add(Implies(flower_vars[i] == flowers.index("roses"), color_vars[i] == colors.index("white")))

    # Clue 11: There is one house between the person who loves a carnations arrangement and the person whose favorite color is red.
    for i in range(n):
        for j in range(n):
            s.add(Implies(And(flower_vars[i] == flowers.index("carnations"), color_vars[j] == colors.index("red")),
                          Or(i == j + 2, j == i + 2)))

    # Clue 12: The person who loves cooking is somewhere to the left of the person who paints as a hobby.
    for i in range(n):
        for j in range(n):
            s.add(Implies(And(hobby_vars[i] == hobbies.index("cooking"), hobby_vars[j] == hobbies.index("painting")), i < j))

    # Clue 13: The one who only drinks water is in the third house.
    # House 3 -> index 2 must have water.
    s.add(drink_vars[2] == drinks.index("water"))

    # Clue 14: The person who loves a carnations arrangement is the root beer lover.
    for i in range(n):
        s.add(Implies(flower_vars[i] == flowers.index("carnations"), drink_vars[i] == drinks.index("root beer")))
        s.add(Implies(drink_vars[i] == drinks.index("root beer"), flower_vars[i] == flowers.index("carnations")))

    # Clue 15: The person who loves white is in the second house.
    # House 2 -> index 1 must have white.
    s.add(color_vars[1] == colors.index("white"))

    if s.check() == sat:
        m = s.model()
        solution_rows = []
        for i in range(n):
            house_num = str(i + 1)
            name_val = names[m[name_vars[i]].as_long()]
            drink_val = drinks[m[drink_vars[i]].as_long()]
            color_val = colors[m[color_vars[i]].as_long()]
            flower_val = flowers[m[flower_vars[i]].as_long()]
            hobby_val = hobbies[m[hobby_vars[i]].as_long()]
            solution_rows.append([house_num, name_val, drink_val, color_val, flower_val, hobby_val])
        result = {
            "solution": {
                "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    main()