import json
from z3 import Solver, Int, Distinct, And, Or, Abs

def solve():
    houses = range(1, 7)

    Names = ["Alice", "Peter", "Eric", "Bob", "Arnold", "Carol"]
    Cigars = ["pall mall", "yellow monster", "dunhill", "blue master", "prince", "blends"]
    Music = ["hip hop", "jazz", "country", "pop", "classical", "rock"]
    Drinks = ["water", "milk", "boba tea", "tea", "root beer", "coffee"]
    Mothers = ["Kailyn", "Penny", "Janelle", "Holly", "Sarah", "Aniya"]
    Foods = ["soup", "pizza", "spaghetti", "stir fry", "stew", "grilled cheese"]

    # Create Z3 variables for each attribute value representing the house position (1..6)
    def make_vars(values, prefix):
        return {v: Int(f"{prefix}_{v.replace(' ', '_')}") for v in values}

    name_pos = make_vars(Names, "Name")
    cigar_pos = make_vars(Cigars, "Cigar")
    music_pos = make_vars(Music, "Music")
    drink_pos = make_vars(Drinks, "Drink")
    mother_pos = make_vars(Mothers, "Mother")
    food_pos = make_vars(Foods, "Food")

    s = Solver()

    # Domain constraints: every variable is in 1..6
    for cat in (name_pos, cigar_pos, music_pos, drink_pos, mother_pos, food_pos):
        for v in cat.values():
            s.add(And(v >= 1, v <= 6))
        # Uniqueness within category
        s.add(Distinct(*cat.values()))

    # Helper lambdas
    def directly_left(a, b):
        s.add(a + 1 == b)

    def somewhere_left(a, b):
        s.add(a < b)

    def somewhere_right(a, b):
        s.add(a > b)

    # Apply clues:

    # 1. Carol is directly left of the person who loves eating grilled cheese.
    directly_left(name_pos["Carol"], food_pos["grilled cheese"])

    # 2. Eric is not in the second house.
    s.add(name_pos["Eric"] != 2)

    # 3. The person whose mother's name is Holly is somewhere to the right of Carol.
    somewhere_right(mother_pos["Holly"], name_pos["Carol"])

    # 4. The person who loves eating grilled cheese is somewhere to the right of the person who loves rock music.
    somewhere_right(food_pos["grilled cheese"], music_pos["rock"])

    # 5. Eric is directly left of Carol.
    directly_left(name_pos["Eric"], name_pos["Carol"])

    # 6. The person who loves pop music is not in the third house.
    s.add(music_pos["pop"] != 3)

    # 7. Eric is the person who loves country music.
    s.add(name_pos["Eric"] == music_pos["country"])

    # 8. The person who loves classical music is in the sixth house.
    s.add(music_pos["classical"] == 6)

    # 9. The coffee drinker is Bob.
    s.add(drink_pos["coffee"] == name_pos["Bob"])

    # 10. The person who smokes many unique blends is Peter.
    s.add(cigar_pos["blends"] == name_pos["Peter"])

    # 11. The person who loves the stew is not in the fifth house.
    s.add(food_pos["stew"] != 5)

    # 12. The root beer lover is directly left of The person whose mother's name is Janelle.
    directly_left(drink_pos["root beer"], mother_pos["Janelle"])

    # 13. There are two houses between Sarah and Yellow Monster smoker. (difference of 3)
    s.add(Abs(mother_pos["Sarah"] - cigar_pos["yellow monster"]) == 3)

    # 14. Eric is the tea drinker.
    s.add(name_pos["Eric"] == drink_pos["tea"])

    # 15. Pall Mall is somewhere to the right of the person who loves stir fry.
    somewhere_right(cigar_pos["pall mall"], food_pos["stir fry"])

    # 16. The person who loves the soup is Bob.
    s.add(food_pos["soup"] == name_pos["Bob"])

    # 17. Hip-hop music is directly left of Kailyn.
    directly_left(music_pos["hip hop"], mother_pos["Kailyn"])

    # 18. Arnold is somewhere to the right of Kailyn.
    somewhere_right(name_pos["Arnold"], mother_pos["Kailyn"])

    # 19. Water is directly left of Blue Master.
    directly_left(drink_pos["water"], cigar_pos["blue master"])

    # 20. Spaghetti is somewhere to the left of Blends smoker (Peter).
    somewhere_left(food_pos["spaghetti"], cigar_pos["blends"])

    # 21. Sarah is directly left of Jazz.
    directly_left(mother_pos["Sarah"], music_pos["jazz"])

    # 22. Hip-hop is directly left of Root Beer.
    directly_left(music_pos["hip hop"], drink_pos["root beer"])

    # 23. Water drinker is the person who loves the stew.
    s.add(drink_pos["water"] == food_pos["stew"])

    # 24. Dunhill smoker is not in the second house.
    s.add(cigar_pos["dunhill"] != 2)

    # 25. Milk drinker is Janelle.
    s.add(drink_pos["milk"] == mother_pos["Janelle"])

    # 26. Eric is Aniya's child.
    s.add(name_pos["Eric"] == mother_pos["Aniya"])

    if s.check() != 1:  # 1 == sat
        raise RuntimeError("No solution found")

    m = s.model()

    # Build inverse maps from house -> value
    def invert(cat_pos):
        inv = {}
        for k, v in cat_pos.items():
            inv[int(m[v].as_long())] = k
        return inv

    inv_name = invert(name_pos)
    inv_cigar = invert(cigar_pos)
    inv_music = invert(music_pos)
    inv_drink = invert(drink_pos)
    inv_mother = invert(mother_pos)
    inv_food = invert(food_pos)

    # Prepare JSON output
    header = ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"]
    rows = []
    for h in houses:
        row = [
            str(h),
            inv_name[h],
            inv_cigar[h],
            inv_music[h],
            inv_drink[h],
            inv_mother[h],
            inv_food[h],
        ]
        rows.append(row)

    out = {"solution": {"header": header, "rows": rows}}
    print(json.dumps(out, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve()