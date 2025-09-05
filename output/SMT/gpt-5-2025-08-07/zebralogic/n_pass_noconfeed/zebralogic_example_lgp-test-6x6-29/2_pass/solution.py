import json
from z3 import Solver, Int, Distinct, And, Abs, sat

def main():
    houses = range(1, 7)  # 1..6

    Names = ['Arnold', 'Carol', 'Peter', 'Eric', 'Bob', 'Alice']
    HouseStyles = ['ranch', 'colonial', 'modern', 'craftsman', 'mediterranean', 'victorian']
    Foods = ['pizza', 'stew', 'spaghetti', 'grilled cheese', 'stir fry', 'soup']
    Vacations = ['cultural', 'cruise', 'mountain', 'camping', 'city', 'beach']
    Heights = ['average', 'very tall', 'very short', 'short', 'tall', 'super tall']
    Cigars = ['yellow monster', 'prince', 'dunhill', 'pall mall', 'blue master', 'blends']

    # Create Z3 variables: position (1..6) for each attribute value
    name_pos = {n: Int(f"name_{n}") for n in Names}
    style_pos = {s: Int(f"style_{s}") for s in HouseStyles}
    food_pos = {f: Int(f"food_{f.replace(' ', '_')}") for f in Foods}
    vac_pos = {v: Int(f"vac_{v.replace(' ', '_')}") for v in Vacations}
    height_pos = {h: Int(f"height_{h.replace(' ', '_')}") for h in Heights}
    cigar_pos = {c: Int(f"cigar_{c.replace(' ', '_')}") for c in Cigars}

    s = Solver()

    # Domain constraints
    for d in [name_pos, style_pos, food_pos, vac_pos, height_pos, cigar_pos]:
        for v in d.values():
            s.add(And(v >= 1, v <= 6))

    # AllDifferent per category
    s.add(Distinct([name_pos[n] for n in Names]))
    s.add(Distinct([style_pos[sx] for sx in HouseStyles]))
    s.add(Distinct([food_pos[f] for f in Foods]))
    s.add(Distinct([vac_pos[v] for v in Vacations]))
    s.add(Distinct([height_pos[h] for h in Heights]))
    s.add(Distinct([cigar_pos[c] for c in Cigars]))

    # Clues
    # 1. Alice is in the fifth house.
    s.add(name_pos['Alice'] == 5)

    # 2. The person who loves stir fry is the person living in a colonial-style house.
    s.add(food_pos['stir fry'] == style_pos['colonial'])

    # 3. Alice is the person who loves the spaghetti eater. (Interpret as: Alice loves spaghetti)
    s.add(food_pos['spaghetti'] == name_pos['Alice'])

    # 4. Arnold is the person who loves the stew.
    s.add(food_pos['stew'] == name_pos['Arnold'])

    # 5. There is one house between the person who has an average height and Peter.
    s.add(Abs(height_pos['average'] - name_pos['Peter']) == 2)

    # 6. The person in a Craftsman-style house is not in the third house.
    s.add(style_pos['craftsman'] != 3)

    # 7. The person who has an average height is the person who loves stir fry.
    s.add(height_pos['average'] == food_pos['stir fry'])

    # 8. The person who loves beach vacations is the person in a ranch-style home.
    s.add(vac_pos['beach'] == style_pos['ranch'])

    # 9. Eric is in the fourth house.
    s.add(name_pos['Eric'] == 4)

    # 10. There is one house between the person living in a colonial-style house and the person who enjoys camping trips.
    s.add(Abs(style_pos['colonial'] - vac_pos['camping']) == 2)

    # 11. The person who enjoys mountain retreats is the person who smokes Yellow Monster.
    s.add(vac_pos['mountain'] == cigar_pos['yellow monster'])

    # 12. The person who enjoys mountain retreats is the person who is very tall.
    s.add(vac_pos['mountain'] == height_pos['very tall'])

    # 13. The person who enjoys mountain retreats and the Dunhill smoker are next to each other.
    s.add(Abs(vac_pos['mountain'] - cigar_pos['dunhill']) == 1)

    # 14. The person who loves the spaghetti eater is the person residing in a Victorian house. (Interpret as: spaghetti -> Victorian)
    s.add(food_pos['spaghetti'] == style_pos['victorian'])

    # 15. The person who is tall is the person who loves beach vacations.
    s.add(height_pos['tall'] == vac_pos['beach'])

    # 16. The person who is tall is somewhere to the left of the person residing in a Victorian house.
    s.add(height_pos['tall'] < style_pos['victorian'])

    # 17. The person who loves stir fry is directly left of Bob.
    s.add(food_pos['stir fry'] + 1 == name_pos['Bob'])

    # 18. The person in a modern-style house is somewhere to the left of Alice.
    s.add(style_pos['modern'] < name_pos['Alice'])

    # 19. The person in a Craftsman-style house is somewhere to the left of the person who is short.
    s.add(style_pos['craftsman'] < height_pos['short'])

    # 20. The person who loves stir fry is somewhere to the left of the Prince smoker.
    s.add(food_pos['stir fry'] < cigar_pos['prince'])

    # 21. There are two houses between the person who loves eating grilled cheese and the person who is super tall.
    s.add(Abs(food_pos['grilled cheese'] - height_pos['super tall']) == 3)

    # 22. The person in a ranch-style home is the person who smokes Blue Master.
    s.add(style_pos['ranch'] == cigar_pos['blue master'])

    # 23. The person who smokes many unique blends is directly left of the person who smokes Blue Master.
    s.add(cigar_pos['blends'] + 1 == cigar_pos['blue master'])

    # 24. The person who goes on cultural tours is the person who is a pizza lover.
    s.add(vac_pos['cultural'] == food_pos['pizza'])

    # 25. The person who is a pizza lover is somewhere to the left of the person who likes going on cruises.
    s.add(food_pos['pizza'] < vac_pos['cruise'])

    if s.check() != sat:
        raise Exception("No solution found")

    m = s.model()

    # Invert mapping: for each house, find attribute value at that position
    def invert_map(d):
        inv = {}
        for k, v in d.items():
            inv[m[v].as_long()] = k
        return inv

    inv_name = invert_map(name_pos)
    inv_style = invert_map(style_pos)
    inv_food = invert_map(food_pos)
    inv_vac = invert_map(vac_pos)
    inv_height = invert_map(height_pos)
    inv_cigar = invert_map(cigar_pos)

    rows = []
    for h in houses:
        row = [
            str(h),
            inv_name[h],
            inv_style[h],
            inv_food[h],
            inv_vac[h],
            inv_height[h],
            inv_cigar[h],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"],
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()