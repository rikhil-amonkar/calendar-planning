from z3 import *
import json

def main():
    solver = Solver()

    # Define mappings for each attribute
    names_map = {"Alice": 0, "Peter": 1, "Eric": 2, "Bob": 3, "Arnold": 4, "Carol": 5}
    cigars_map = {"pall mall": 0, "yellow monster": 1, "dunhill": 2, "blue master": 3, "prince": 4, "blends": 5}
    music_map = {"hip hop": 0, "jazz": 1, "country": 2, "pop": 3, "classical": 4, "rock": 5}
    drinks_map = {"water": 0, "milk": 1, "boba tea": 2, "tea": 3, "root beer": 4, "coffee": 5}
    mothers_map = {"Kailyn": 0, "Penny": 1, "Janelle": 2, "Holly": 3, "Sarah": 4, "Aniya": 5}
    foods_map = {"soup": 0, "pizza": 1, "spaghetti": 2, "stir fry": 3, "stew": 4, "grilled cheese": 5}

    # Create inverse mappings for output
    inv_names = {v: k for k, v in names_map.items()}
    inv_cigars = {v: k for k, v in cigars_map.items()}
    inv_music = {v: k for k, v in music_map.items()}
    inv_drinks = {v: k for k, v in drinks_map.items()}
    inv_mothers = {v: k for k, v in mothers_map.items()}
    inv_foods = {v: k for k, v in foods_map.items()}

    n = 6  # Number of houses
    # Create variables for each house and each attribute
    name_vars   = [Int(f"name_{i}") for i in range(n)]
    cigar_vars  = [Int(f"cigar_{i}") for i in range(n)]
    music_vars  = [Int(f"music_{i}") for i in range(n)]
    drink_vars  = [Int(f"drink_{i}") for i in range(n)]
    mother_vars = [Int(f"mother_{i}") for i in range(n)]
    food_vars   = [Int(f"food_{i}") for i in range(n)]

    # All variables must be in the domain 0..5
    for var in name_vars + cigar_vars + music_vars + drink_vars + mother_vars + food_vars:
        solver.add(var >= 0, var < n)

    # Each attribute list must be a permutation of 0..5 (all different)
    solver.add(Distinct(name_vars))
    solver.add(Distinct(cigar_vars))
    solver.add(Distinct(music_vars))
    solver.add(Distinct(drink_vars))
    solver.add(Distinct(mother_vars))
    solver.add(Distinct(food_vars))

    # 1. Carol is directly left of the person who loves eating grilled cheese.
    for i in range(n):
        if i < n - 1:
            solver.add(Implies(name_vars[i] == names_map["Carol"], food_vars[i+1] == foods_map["grilled cheese"]))
        else:
            solver.add(name_vars[i] != names_map["Carol"])

    # 2. Eric is not in the second house.
    solver.add(name_vars[1] != names_map["Eric"])

    # 3. The person whose mother's name is Holly is somewhere to the right of Carol.
    for i in range(n):
        for j in range(n):
            solver.add(Implies(And(mother_vars[i] == mothers_map["Holly"], name_vars[j] == names_map["Carol"]),
                                i > j))

    # 4. The person who loves grilled cheese is somewhere to the right of the person who loves rock music.
    for i in range(n):
        for j in range(n):
            solver.add(Implies(And(food_vars[i] == foods_map["grilled cheese"], music_vars[j] == music_map["rock"]),
                                i > j))

    # 5. Eric is directly left of Carol.
    for i in range(n):
        if i < n - 1:
            solver.add(Implies(name_vars[i] == names_map["Eric"], name_vars[i+1] == names_map["Carol"]))
        else:
            solver.add(name_vars[i] != names_map["Eric"])

    # 6. The person who loves pop music is not in the third house.
    solver.add(music_vars[2] != music_map["pop"])

    # 7. Eric is the person who loves country music.
    for i in range(n):
        solver.add(Implies(name_vars[i] == names_map["Eric"], music_vars[i] == music_map["country"]))

    # 8. The person who loves classical music is in the sixth house.
    solver.add(music_vars[5] == music_map["classical"])

    # 9. The coffee drinker is Bob.
    for i in range(n):
        solver.add(Implies(name_vars[i] == names_map["Bob"], drink_vars[i] == drinks_map["coffee"]))

    # 10. The person who smokes many unique blends is Peter.
    for i in range(n):
        solver.add(Implies(name_vars[i] == names_map["Peter"], cigar_vars[i] == cigars_map["blends"]))
        solver.add(Implies(cigar_vars[i] == cigars_map["blends"], name_vars[i] == names_map["Peter"]))

    # 11. The person who loves the stew is not in the fifth house.
    solver.add(food_vars[4] != foods_map["stew"])

    # 12. The root beer lover is directly left of the person whose mother's name is Janelle.
    for i in range(n):
        if i < n - 1:
            solver.add(Implies(drink_vars[i] == drinks_map["root beer"], mother_vars[i+1] == mothers_map["Janelle"]))
        else:
            solver.add(drink_vars[i] != drinks_map["root beer"])

    # 13. There are two houses between the person whose mother's name is Sarah and the person who smokes Yellow Monster.
    for i in range(n):
        for j in range(n):
            solver.add(Implies(And(cigar_vars[i] == cigars_map["yellow monster"], mother_vars[j] == mothers_map["Sarah"]),
                                Or(i == j + 3, j == i + 3)))

    # 14. Eric is the tea drinker.
    for i in range(n):
        solver.add(Implies(name_vars[i] == names_map["Eric"], drink_vars[i] == drinks_map["tea"]))

    # 15. The person partial to Pall Mall is somewhere to the right of the person who loves stir fry.
    for i in range(n):
        for j in range(n):
            solver.add(Implies(And(cigar_vars[i] == cigars_map["pall mall"], food_vars[j] == foods_map["stir fry"]),
                                i > j))

    # 16. The person who loves the soup is Bob.
    for i in range(n):
        solver.add(Implies(name_vars[i] == names_map["Bob"], food_vars[i] == foods_map["soup"]))

    # 17. The person who loves hip-hop music is directly left of the person whose mother's name is Kailyn.
    for i in range(n):
        if i < n - 1:
            solver.add(Implies(music_vars[i] == music_map["hip hop"], mother_vars[i+1] == mothers_map["Kailyn"]))
        else:
            solver.add(music_vars[i] != music_map["hip hop"])

    # 18. Arnold is somewhere to the right of the person whose mother's name is Kailyn.
    for i in range(n):
        for j in range(n):
            solver.add(Implies(And(name_vars[i] == names_map["Arnold"], mother_vars[j] == mothers_map["Kailyn"]),
                                i > j))

    # 19. The one who only drinks water is directly left of the person who smokes Blue Master.
    for i in range(n):
        if i < n - 1:
            solver.add(Implies(drink_vars[i] == drinks_map["water"], cigar_vars[i+1] == cigars_map["blue master"]))
        else:
            solver.add(drink_vars[i] != drinks_map["water"])

    # 20. The person who loves spaghetti is somewhere to the left of the person who smokes many unique blends.
    for i in range(n):
        for j in range(n):
            solver.add(Implies(And(food_vars[i] == foods_map["spaghetti"], cigar_vars[j] == cigars_map["blends"]),
                                i < j))

    # 21. The person whose mother's name is Sarah is directly left of the person who loves jazz music.
    for i in range(n):
        if i < n - 1:
            solver.add(Implies(mother_vars[i] == mothers_map["Sarah"], music_vars[i+1] == music_map["jazz"]))
        else:
            solver.add(mother_vars[i] != mothers_map["Sarah"])

    # 22. The person who loves hip-hop music is directly left of the root beer lover.
    for i in range(n):
        if i < n - 1:
            solver.add(Implies(music_vars[i] == music_map["hip hop"], drink_vars[i+1] == drinks_map["root beer"]))
        else:
            solver.add(music_vars[i] != music_map["hip hop"])

    # 23. The one who only drinks water is the person who loves the stew.
    for i in range(n):
        solver.add(Implies(drink_vars[i] == drinks_map["water"], food_vars[i] == foods_map["stew"]))
        solver.add(Implies(food_vars[i] == foods_map["stew"], drink_vars[i] == drinks_map["water"]))

    # 24. The Dunhill smoker is not in the second house.
    solver.add(cigar_vars[1] != cigars_map["dunhill"])

    # 25. The person who likes milk is the person whose mother's name is Janelle.
    for i in range(n):
        solver.add(Implies(drink_vars[i] == drinks_map["milk"], mother_vars[i] == mothers_map["Janelle"]))
        solver.add(Implies(mother_vars[i] == mothers_map["Janelle"], drink_vars[i] == drinks_map["milk"]))

    # 26. Eric is the person whose mother's name is Aniya.
    for i in range(n):
        solver.add(Implies(name_vars[i] == names_map["Eric"], mother_vars[i] == mothers_map["Aniya"]))

    # Solve the puzzle
    if solver.check() == sat:
        model = solver.model()
        solution_rows = []
        for i in range(n):
            house = str(i + 1)
            name_val   = inv_names[model.evaluate(name_vars[i]).as_long()]
            cigar_val  = inv_cigars[model.evaluate(cigar_vars[i]).as_long()]
            music_val  = inv_music[model.evaluate(music_vars[i]).as_long()]
            drink_val  = inv_drinks[model.evaluate(drink_vars[i]).as_long()]
            mother_val = inv_mothers[model.evaluate(mother_vars[i]).as_long()]
            food_val   = inv_foods[model.evaluate(food_vars[i]).as_long()]
            solution_rows.append([house, name_val, cigar_val, music_val, drink_val, mother_val, food_val])
        output = {
            "solution": {
                "header": ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"],
                "rows": solution_rows
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    main()