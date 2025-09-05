import json
from z3 import Solver, Int, Distinct, And, Or, If, Abs

def sanitize(s):
    return s.lower().replace(" ", "_").replace("-", "_")

def main():
    houses = range(1, 7)

    Names = ["Alice", "Peter", "Eric", "Bob", "Arnold", "Carol"]
    Cigars = ["pall mall", "yellow monster", "dunhill", "blue master", "prince", "blends"]
    Music = ["hip hop", "jazz", "country", "pop", "classical", "rock"]
    Drinks = ["water", "milk", "boba tea", "tea", "root beer", "coffee"]
    Mothers = ["Kailyn", "Penny", "Janelle", "Holly", "Sarah", "Aniya"]
    Food = ["soup", "pizza", "spaghetti", "stir fry", "stew", "grilled cheese"]

    # Create Z3 variables for positions (1..6) for each attribute value
    pos_name = {n: Int(f"pos_name_{sanitize(n)}") for n in Names}
    pos_cigar = {c: Int(f"pos_cigar_{sanitize(c)}") for c in Cigars}
    pos_music = {m: Int(f"pos_music_{sanitize(m)}") for m in Music}
    pos_drink = {d: Int(f"pos_drink_{sanitize(d)}") for d in Drinks}
    pos_mother = {m: Int(f"pos_mother_{sanitize(m)}") for m in Mothers}
    pos_food = {f: Int(f"pos_food_{sanitize(f)}") for f in Food}

    s = Solver()

    # Domain constraints
    for d in [pos_name, pos_cigar, pos_music, pos_drink, pos_mother, pos_food]:
        for v in d.values():
            s.add(And(v >= 1, v <= 6))

    # All-different constraints within each category
    s.add(Distinct([pos_name[n] for n in Names]))
    s.add(Distinct([pos_cigar[c] for c in Cigars]))
    s.add(Distinct([pos_music[m] for m in Music]))
    s.add(Distinct([pos_drink[d] for d in Drinks]))
    s.add(Distinct([pos_mother[m] for m in Mothers]))
    s.add(Distinct([pos_food[f] for f in Food]))

    # Clues:

    # 1. Carol is directly left of the person who loves eating grilled cheese.
    s.add(pos_name["Carol"] + 1 == pos_food["grilled cheese"])

    # 2. Eric is not in the second house.
    s.add(pos_name["Eric"] != 2)

    # 3. The person whose mother's name is Holly is somewhere to the right of Carol.
    s.add(pos_mother["Holly"] > pos_name["Carol"])

    # 4. The person who loves eating grilled cheese is somewhere to the right of the person who loves rock music.
    s.add(pos_food["grilled cheese"] > pos_music["rock"])

    # 5. Eric is directly left of Carol.
    s.add(pos_name["Eric"] + 1 == pos_name["Carol"])

    # 6. The person who loves pop music is not in the third house.
    s.add(pos_music["pop"] != 3)

    # 7. Eric is the person who loves country music.
    s.add(pos_name["Eric"] == pos_music["country"])

    # 8. The person who loves classical music is in the sixth house.
    s.add(pos_music["classical"] == 6)

    # 9. The coffee drinker is Bob.
    s.add(pos_drink["coffee"] == pos_name["Bob"])

    # 10. The person who smokes many unique blends is Peter.
    s.add(pos_cigar["blends"] == pos_name["Peter"])

    # 11. The person who loves the stew is not in the fifth house.
    s.add(pos_food["stew"] != 5)

    # 12. The root beer lover is directly left of The person whose mother's name is Janelle.
    s.add(pos_drink["root beer"] + 1 == pos_mother["Janelle"])

    # 13. There are two houses between The person whose mother's name is Sarah and the person who smokes Yellow Monster.
    s.add(Abs(pos_mother["Sarah"] - pos_cigar["yellow monster"]) == 3)

    # 14. Eric is the tea drinker.
    s.add(pos_name["Eric"] == pos_drink["tea"])

    # 15. The person partial to Pall Mall is somewhere to the right of the person who loves stir fry.
    s.add(pos_cigar["pall mall"] > pos_food["stir fry"])

    # 16. The person who loves the soup is Bob.
    s.add(pos_food["soup"] == pos_name["Bob"])

    # 17. The person who loves hip-hop music is directly left of The person whose mother's name is Kailyn.
    s.add(pos_music["hip hop"] + 1 == pos_mother["Kailyn"])

    # 18. Arnold is somewhere to the right of The person whose mother's name is Kailyn.
    s.add(pos_name["Arnold"] > pos_mother["Kailyn"])

    # 19. The one who only drinks water is directly left of the person who smokes Blue Master.
    s.add(pos_drink["water"] + 1 == pos_cigar["blue master"])

    # 20. The person who loves the spaghetti eater is somewhere to the left of the person who smokes many unique blends.
    # Interpreted as: The spaghetti eater is somewhere to the left of the blends smoker (Peter).
    s.add(pos_food["spaghetti"] < pos_cigar["blends"])

    # 21. The person whose mother's name is Sarah is directly left of the person who loves jazz music.
    s.add(pos_mother["Sarah"] + 1 == pos_music["jazz"])

    # 22. The person who loves hip-hop music is directly left of the root beer lover.
    s.add(pos_music["hip hop"] + 1 == pos_drink["root beer"])

    # 23. The one who only drinks water is the person who loves the stew.
    s.add(pos_drink["water"] == pos_food["stew"])

    # 24. The Dunhill smoker is not in the second house.
    s.add(pos_cigar["dunhill"] != 2)

    # 25. The person who likes milk is The person whose mother's name is Janelle.
    s.add(pos_drink["milk"] == pos_mother["Janelle"])

    # 26. Eric is The person whose mother's name is Aniya.
    s.add(pos_name["Eric"] == pos_mother["Aniya"])

    if s.check() != True:
        # Fallback JSON if unsat (should not happen for a valid puzzle)
        out = {
            "solution": {
                "header": ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"],
                "rows": []
            }
        }
        print(json.dumps(out))
        return

    m = s.model()

    # Invert mappings to get attribute value at each house
    def invert(pos_map, values):
        inv = {}
        for val in values:
            h = m[pos_map[val]].as_long()
            inv[h] = val
        return inv

    inv_name = invert(pos_name, Names)
    inv_cigar = invert(pos_cigar, Cigars)
    inv_music = invert(pos_music, Music)
    inv_drink = invert(pos_drink, Drinks)
    inv_mother = invert(pos_mother, Mothers)
    inv_food = invert(pos_food, Food)

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

    output = {
        "solution": {
            "header": ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()