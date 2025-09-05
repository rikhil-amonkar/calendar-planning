import json
from z3 import Int, Solver, Distinct, Or, And

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]

    Names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
    Smoothies = ["lime", "dragonfruit", "desert", "watermelon", "cherry"]
    Animals = ["horse", "dog", "bird", "fish", "cat"]
    Nationalities = ["german", "swede", "norwegian", "brit", "dane"]

    # Create position variables for each attribute value
    name_pos = {n: Int(f"name_{n}") for n in Names}
    smoothie_pos = {d: Int(f"smoothie_{d}") for d in Smoothies}
    animal_pos = {a: Int(f"animal_{a}") for a in Animals}
    nat_pos = {na: Int(f"nat_{na}") for na in Nationalities}

    s = Solver()

    # Domain constraints: each position between 1 and 5
    for d in name_pos.values():
        s.add(And(d >= 1, d <= 5))
    for d in smoothie_pos.values():
        s.add(And(d >= 1, d <= 5))
    for d in animal_pos.values():
        s.add(And(d >= 1, d <= 5))
    for d in nat_pos.values():
        s.add(And(d >= 1, d <= 5))

    # All-different constraints per category
    s.add(Distinct(*name_pos.values()))
    s.add(Distinct(*smoothie_pos.values()))
    s.add(Distinct(*animal_pos.values()))
    s.add(Distinct(*nat_pos.values()))

    # Clues:
    # 1. The Swedish person is directly left of the dog owner.
    s.add(nat_pos["swede"] + 1 == animal_pos["dog"])

    # 2. There are two houses between the dog owner and the British person.
    s.add(Or(nat_pos["brit"] == animal_pos["dog"] + 3,
             animal_pos["dog"] == nat_pos["brit"] + 3))

    # 3. The Dane is the person who keeps horses.
    s.add(nat_pos["dane"] == animal_pos["horse"])

    # 4. The bird keeper is somewhere to the right of the cat lover.
    s.add(animal_pos["bird"] > animal_pos["cat"])

    # 5. The dog owner is directly left of the person who drinks Lime smoothies.
    s.add(animal_pos["dog"] + 1 == smoothie_pos["lime"])

    # 6. Eric is the cat lover.
    s.add(name_pos["Eric"] == animal_pos["cat"])

    # 7. Bob is the bird keeper.
    s.add(name_pos["Bob"] == animal_pos["bird"])

    # 8. The person who likes Cherry smoothies is directly left of Peter.
    s.add(smoothie_pos["cherry"] + 1 == name_pos["Peter"])

    # 9. The bird keeper is the Watermelon smoothie lover.
    s.add(animal_pos["bird"] == smoothie_pos["watermelon"])

    # 10. The Desert smoothie lover is the dog owner.
    s.add(smoothie_pos["desert"] == animal_pos["dog"])

    # 11. The person who keeps horses is in the third house.
    s.add(animal_pos["horse"] == 3)

    # 12. The Norwegian is Alice.
    s.add(nat_pos["norwegian"] == name_pos["Alice"])

    if s.check() != 1:  # 1 == sat
        return {"solution": {"header": ["House", "Name", "Smoothie", "Animal", "Nationality"], "rows": []}}

    m = s.model()

    # Build inverse maps: house -> attribute value
    def invert(mapping):
        inv = {}
        for k, v in mapping.items():
            inv[m[v].as_long()] = k
        return inv

    inv_name = invert(name_pos)
    inv_smoothie = invert(smoothie_pos)
    inv_animal = invert(animal_pos)
    inv_nat = invert(nat_pos)

    rows = []
    for h in houses:
        rows.append([
            str(h),
            inv_name[h],
            inv_smoothie[h],
            inv_animal[h],
            inv_nat[h],
        ])

    return {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))