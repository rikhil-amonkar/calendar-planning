import json
from z3 import Solver, Int, Distinct, Or, And, sat

def solve():
    houses = range(1, 7)

    # Categories and their values
    Names = ["Peter", "Carol", "Eric", "Alice", "Bob", "Arnold"]
    Phones = ["huawei p50", "google pixel 6", "xiaomi mi 11", "iphone 13", "samsung galaxy s21", "oneplus 9"]
    Cigars = ["dunhill", "pall mall", "blends", "blue master", "prince", "yellow monster"]
    Flowers = ["daffodils", "carnations", "roses", "tulips", "lilies", "iris"]
    Colors = ["yellow", "red", "green", "blue", "white", "purple"]
    Sports = ["soccer", "tennis", "basketball", "volleyball", "swimming", "baseball"]

    # Create Z3 variables for positions of each value (house index 1..6)
    def make_vars(values):
        return {v: Int(v.replace(" ", "_")) for v in values}

    name = make_vars(Names)
    phone = make_vars(Phones)
    cigar = make_vars(Cigars)
    flower = make_vars(Flowers)
    color = make_vars(Colors)
    sport = make_vars(Sports)

    s = Solver()

    # Domain constraints: all positions are in 1..6
    for d in [name, phone, cigar, flower, color, sport]:
        for v in d.values():
            s.add(And(v >= 1, v <= 6))
        s.add(Distinct(*d.values()))

    # Helper predicates
    def left_of(a, b):
        return a < b

    def directly_left_of(a, b):
        return a + 1 == b

    def next_to(a, b):
        return Or(a == b + 1, a + 1 == b)

    def distance(a, b, k):
        return Or(a == b + k, b == a + k)

    # Clues:

    # 1. OnePlus 9 in the second house.
    s.add(phone["oneplus 9"] == 2)

    # 2. Xiaomi Mi 11 is somewhere to the left of Huawei P50.
    s.add(left_of(phone["xiaomi mi 11"], phone["huawei p50"]))

    # 3. Carol loves carnations.
    s.add(name["Carol"] == flower["carnations"])

    # 4. Purple is directly left of Pall Mall.
    s.add(directly_left_of(color["purple"], cigar["pall mall"]))

    # 5. Green is Blue Master.
    s.add(color["green"] == cigar["blue master"])

    # 6. Yellow and Blue are next to each other.
    s.add(next_to(color["yellow"], color["blue"]))

    # 7. Eric is somewhere to the right of Samsung Galaxy S21.
    s.add(name["Eric"] > phone["samsung galaxy s21"])

    # 8. Two houses between Carol and Daffodils.
    s.add(distance(name["Carol"], flower["daffodils"], 3))

    # 9. Prince smoker loves basketball.
    s.add(cigar["prince"] == sport["basketball"])

    # 10. Dunhill smoker loves volleyball.
    s.add(cigar["dunhill"] == sport["volleyball"])

    # 11. Swimming is Google Pixel 6.
    s.add(sport["swimming"] == phone["google pixel 6"])

    # 12. Huawei P50 is directly left of White.
    s.add(directly_left_of(phone["huawei p50"], color["white"]))

    # 13. OnePlus 9 and Roses are next to each other.
    s.add(next_to(phone["oneplus 9"], flower["roses"]))

    # 14. Iris is somewhere to the left of Eric.
    s.add(left_of(flower["iris"], name["Eric"]))

    # 15. Dunhill smoker is Peter.
    s.add(cigar["dunhill"] == name["Peter"])

    # 16. The person who loves Blue is Peter.
    s.add(color["blue"] == name["Peter"])

    # 17. Tulips is Bob.
    s.add(flower["tulips"] == name["Bob"])

    # 18. Alice is in the first house.
    s.add(name["Alice"] == 1)

    # 19. Baseball is directly left of Blue Master.
    s.add(directly_left_of(sport["baseball"], cigar["blue master"]))

    # 20. Google Pixel 6 is somewhere to the right of Blends.
    s.add(phone["google pixel 6"] > cigar["blends"])

    # 21. Soccer is Carol.
    s.add(sport["soccer"] == name["Carol"])

    # 22. Carnations directly left of Blends smoker.
    s.add(directly_left_of(flower["carnations"], cigar["blends"]))

    # 23. Eric is the Blends smoker.
    s.add(name["Eric"] == cigar["blends"])

    # 24. Volleyball is iPhone 13.
    s.add(sport["volleyball"] == phone["iphone 13"])

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Build reverse lookup for each house
    def invert(category_dict):
        # returns list index by house (1..6) -> value string
        inv = [""] * 7  # ignore index 0
        for k, v in category_dict.items():
            inv[m.eval(v).as_long()] = k
        return inv

    name_at = invert(name)
    phone_at = invert(phone)
    cigar_at = invert(cigar)
    flower_at = invert(flower)
    color_at = invert(color)
    sport_at = invert(sport)

    header = ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"]
    rows = []
    for h in houses:
        rows.append([
            str(h),
            name_at[h],
            phone_at[h],
            cigar_at[h],
            flower_at[h],
            color_at[h],
            sport_at[h],
        ])

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve()
    print(json.dumps(solution, ensure_ascii=False))