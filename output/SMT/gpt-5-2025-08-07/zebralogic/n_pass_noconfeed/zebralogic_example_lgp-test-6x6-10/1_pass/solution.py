import json
import re
from z3 import Solver, Int, Distinct, And

def sanitize(label):
    return re.sub(r'[^A-Za-z0-9_]', '_', label.lower())

def make_pos_vars(category_name, labels, n):
    return {label: Int(f"pos_{category_name}_{sanitize(label)}") for label in labels}

def add_domain_and_distinct(s, pos_vars, n):
    vars_list = list(pos_vars.values())
    for v in vars_list:
        s.add(And(v >= 1, v <= n))
    s.add(Distinct(vars_list))

def main():
    n = 6
    houses = list(range(1, n+1))

    # Categories and labels
    Names = ["Arnold", "Bob", "Peter", "Alice", "Carol", "Eric"]
    Foods = ["stew", "grilled cheese", "stir fry", "soup", "pizza", "spaghetti"]
    Heights = ["tall", "average", "super tall", "very short", "very tall", "short"]
    Drinks = ["root beer", "boba tea", "coffee", "water", "tea", "milk"]
    Pets = ["hamster", "fish", "cat", "dog", "bird", "rabbit"]
    Phones = ["samsung galaxy s21", "xiaomi mi 11", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9"]

    # Create Z3 variables: position of each attribute value (1..6)
    pos_Name = make_pos_vars("Name", Names, n)
    pos_Food = make_pos_vars("Food", Foods, n)
    pos_Height = make_pos_vars("Height", Heights, n)
    pos_Drink = make_pos_vars("Drink", Drinks, n)
    pos_Pet = make_pos_vars("Pet", Pets, n)
    pos_Phone = make_pos_vars("PhoneModel", Phones, n)

    s = Solver()

    # Domain and distinct constraints within each category
    add_domain_and_distinct(s, pos_Name, n)
    add_domain_and_distinct(s, pos_Food, n)
    add_domain_and_distinct(s, pos_Height, n)
    add_domain_and_distinct(s, pos_Drink, n)
    add_domain_and_distinct(s, pos_Pet, n)
    add_domain_and_distinct(s, pos_Phone, n)

    # Helper references for readability
    N = pos_Name
    F = pos_Food
    H = pos_Height
    D = pos_Drink
    P = pos_Pet
    Ph = pos_Phone

    # Clues translated into constraints

    # 1. The person who uses an iPhone 13 is in the third house.
    s.add(Ph["iphone 13"] == 3)

    # 2. Bob is the person who is tall.
    s.add(N["Bob"] == H["tall"])

    # 3. The person who loves the soup is in the second house.
    s.add(F["soup"] == 2)

    # 4. The root beer lover is directly left of the person who uses a Xiaomi Mi 11.
    s.add(D["root beer"] + 1 == Ph["xiaomi mi 11"])

    # 5. The person who uses a Huawei P50 is directly left of the person who loves eating grilled cheese.
    s.add(Ph["huawei p50"] + 1 == F["grilled cheese"])

    # 6. The person who loves stir fry is the person who likes milk.
    s.add(F["stir fry"] == D["milk"])

    # 7. The person who loves eating grilled cheese is the person who is tall.
    s.add(F["grilled cheese"] == H["tall"])

    # 8. The person who uses a Xiaomi Mi 11 is the coffee drinker.
    s.add(Ph["xiaomi mi 11"] == D["coffee"])

    # 9. The person who uses a OnePlus 9 is Arnold.
    s.add(Ph["oneplus 9"] == N["Arnold"])

    # 10. The person who owns a rabbit is not in the fifth house.
    s.add(P["rabbit"] != 5)

    # 11. The person with a pet hamster is somewhere to the right of the person who uses a Google Pixel 6.
    s.add(P["hamster"] > Ph["google pixel 6"])

    # 12. The person who is super tall is the person with an aquarium of fish.
    s.add(H["super tall"] == P["fish"])

    # 13. The person with an aquarium of fish is Alice.
    s.add(P["fish"] == N["Alice"])

    # 14. The tea drinker is directly left of the person who is a pizza lover.
    s.add(D["tea"] + 1 == F["pizza"])

    # 15. The person who uses a Samsung Galaxy S21 is Carol.
    s.add(Ph["samsung galaxy s21"] == N["Carol"])

    # 16. The person who is a pizza lover is the person who is short.
    s.add(F["pizza"] == H["short"])

    # 17. Arnold is the person who is very tall.
    s.add(N["Arnold"] == H["very tall"])

    # 18. The spaghetti eater is the person who uses a Google Pixel 6.
    s.add(F["spaghetti"] == Ph["google pixel 6"])

    # 19. The boba tea drinker is somewhere to the right of the person who loves the soup.
    s.add(D["boba tea"] > F["soup"])

    # 20. The person with a pet hamster is not in the fifth house.
    s.add(P["hamster"] != 5)

    # 21. The person who is very tall is not in the second house.
    s.add(H["very tall"] != 2)

    # 22. The person who is super tall is somewhere to the left of Peter.
    s.add(H["super tall"] < N["Peter"])

    # 23. The person who is very short is the spaghetti eater.
    s.add(H["very short"] == F["spaghetti"])

    # 24. The person who keeps a pet bird is somewhere to the left of the person who loves the spaghetti eater.
    s.add(P["bird"] < F["spaghetti"])

    # 25. The person with an aquarium of fish is directly left of Eric.
    s.add(P["fish"] + 1 == N["Eric"])

    # 26. The person who owns a dog is the person who likes milk.
    s.add(P["dog"] == D["milk"])

    # Derived: Dog owner also eats stir fry from 6 and 26
    s.add(P["dog"] == F["stir fry"])

    # Solve
    if s.check() != 1:
        # Fallback empty (should not happen)
        output = {
            "solution": {
                "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
                "rows": []
            }
        }
        print(json.dumps(output, indent=2))
        return

    m = s.model()

    # Build inverse mappings: house -> label for each category
    def invert(pos_map, labels):
        inv = {i: None for i in houses}
        for label in labels:
            pos = m.evaluate(pos_map[label]).as_long()
            inv[pos] = label
        return inv

    inv_Name = invert(N, Names)
    inv_Food = invert(F, Foods)
    inv_Height = invert(H, Heights)
    inv_Drink = invert(D, Drinks)
    inv_Pet = invert(P, Pets)
    inv_Phone = invert(Ph, Phones)

    rows = []
    for h in houses:
        row = [
            str(h),
            inv_Name[h],
            inv_Food[h],
            inv_Height[h],
            inv_Drink[h],
            inv_Pet[h],
            inv_Phone[h],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
            "rows": rows
        }
    }

    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()