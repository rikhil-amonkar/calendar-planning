from z3 import Solver, Int, Distinct, Abs, sat
import json

def solve_puzzle():
    houses = range(1, 6)

    # Define categories and values
    names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
    smoothies = ["lime", "dragonfruit", "desert", "watermelon", "cherry"]
    animals = ["horse", "dog", "bird", "fish", "cat"]
    nationalities = ["german", "swede", "norwegian", "brit", "dane"]

    # Create Z3 variables for each value in each category (house position 1..5)
    name_vars = {n: Int(f"name_{n}") for n in names}
    smoothie_vars = {s: Int(f"smoothie_{s}") for s in smoothies}
    animal_vars = {a: Int(f"animal_{a}") for a in animals}
    nat_vars = {c: Int(f"nat_{c}") for c in nationalities}

    all_vars = list(name_vars.values()) + list(smoothie_vars.values()) + list(animal_vars.values()) + list(nat_vars.values())

    s = Solver()

    # Domain constraints: each variable is a house 1..5
    for v in all_vars:
        s.add(v >= 1, v <= 5)

    # AllDistinct within each category
    s.add(Distinct(*name_vars.values()))
    s.add(Distinct(*smoothie_vars.values()))
    s.add(Distinct(*animal_vars.values()))
    s.add(Distinct(*nat_vars.values()))

    # Clues as constraints:

    # 1. The Swedish person is directly left of the dog owner.
    s.add(nat_vars["swede"] == animal_vars["dog"] - 1)

    # 2. There are two houses between the dog owner and the British person.
    s.add(Abs(animal_vars["dog"] - nat_vars["brit"]) == 3)

    # 3. The Dane is the person who keeps horses.
    s.add(nat_vars["dane"] == animal_vars["horse"])

    # 4. The bird keeper is somewhere to the right of the cat lover.
    s.add(animal_vars["bird"] > animal_vars["cat"])

    # 5. The dog owner is directly left of the person who drinks Lime smoothies.
    s.add(animal_vars["dog"] == smoothie_vars["lime"] - 1)

    # 6. Eric is the cat lover.
    s.add(name_vars["Eric"] == animal_vars["cat"])

    # 7. Bob is the bird keeper.
    s.add(name_vars["Bob"] == animal_vars["bird"])

    # 8. The person who likes Cherry smoothies is directly left of Peter.
    s.add(smoothie_vars["cherry"] == name_vars["Peter"] - 1)

    # 9. The bird keeper is the Watermelon smoothie lover.
    s.add(animal_vars["bird"] == smoothie_vars["watermelon"])

    # 10. The Desert smoothie lover is the dog owner.
    s.add(smoothie_vars["desert"] == animal_vars["dog"])

    # 11. The person who keeps horses is in the third house.
    s.add(animal_vars["horse"] == 3)

    # 12. The Norwegian is Alice.
    s.add(nat_vars["norwegian"] == name_vars["Alice"])

    assert s.check() == sat, "Puzzle should be solvable."
    m = s.model()

    # Invert mapping: for each house, find the corresponding value for each category
    def value_at_house(var_dict, house_num):
        for key, var in var_dict.items():
            if m.eval(var).as_long() == house_num:
                return key
        return None

    rows = []
    for h in houses:
        name = value_at_house(name_vars, h)
        smoothie = value_at_house(smoothie_vars, h)
        animal = value_at_house(animal_vars, h)
        nat = value_at_house(nat_vars, h)
        rows.append([str(h), name, smoothie, animal, nat])

    output = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))