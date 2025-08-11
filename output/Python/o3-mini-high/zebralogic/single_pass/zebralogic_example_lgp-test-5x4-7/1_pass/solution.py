#!/usr/bin/env python3
import json

def is_valid_partial(houses, i):
    current = houses[i]
    # Internal consistency checks for the current house.
    if current["Name"] == "Eric" and current["animal"] != "cat":
        return False
    if current["Name"] == "Bob" and current["animal"] != "bird":
        return False
    if current["Name"] == "Alice" and current["nationality"] != "norwegian":
        return False
    if current["nationality"] == "norwegian" and current["Name"] != "Alice":
        return False
    if current["smoothie"] == "desert" and current["animal"] != "dog":
        return False
    if current["animal"] == "dog" and current["smoothie"] != "desert":
        return False
    if current["smoothie"] == "watermelon" and current["animal"] != "bird":
        return False
    if current["animal"] == "bird" and current["smoothie"] != "watermelon":
        return False
    # For the third house: must keep horses and be Dane.
    if i == 2:
        if current["animal"] != "horse" or current["nationality"] != "dane":
            return False
    # Check constraints based on the previous (adjacent left) house.
    if i > 0:
        prev = houses[i-1]
        # Clue 8: The person who likes Cherry smoothies is directly left of Peter.
        if prev["smoothie"] == "cherry" and current["Name"] != "Peter":
            return False
        if current["Name"] == "Peter" and prev["smoothie"] != "cherry":
            return False
        # Clue 5: The dog owner is directly left of the person who drinks Lime smoothies.
        if prev["smoothie"] == "desert" and prev["animal"] == "dog" and current["smoothie"] != "lime":
            return False
        if current["smoothie"] == "lime" and (prev["smoothie"] != "desert" or prev["animal"] != "dog"):
            return False
        # Clue 1: The Swedish person is directly left of the dog owner.
        if current["smoothie"] == "desert" and current["animal"] == "dog" and prev["nationality"] != "swede":
            return False
    return True

def global_constraints(houses):
    # Clue 2: There are two houses between the dog owner and the British person.
    dog_index = None
    brit_index = None
    for idx, house in enumerate(houses):
        if house["smoothie"] == "desert" and house["animal"] == "dog":
            dog_index = idx
        if house["nationality"] == "brit":
            brit_index = idx
    if dog_index is None or brit_index is None or abs(dog_index - brit_index) != 3:
        return False
    # Clue 4: The bird keeper is somewhere to the right of the cat lover.
    eric_index = None
    bob_index = None
    for idx, house in enumerate(houses):
        if house["Name"] == "Eric":
            eric_index = idx
        if house["Name"] == "Bob":
            bob_index = idx
    if eric_index is None or bob_index is None or eric_index >= bob_index:
        return False
    return True

def backtrack(i, houses, names, smoothies, animals, nationalities):
    if i == 5:
        if global_constraints(houses):
            yield houses
        return
    for name in names:
        for smoothie in smoothies:
            for animal in animals:
                for nat in nationalities:
                    # For the third house (index 2), enforce Clue 11 and Clue 3:
                    if i == 2:
                        if animal != "horse" or nat != "dane":
                            continue
                    candidate = {
                        "House": str(i+1),
                        "Name": name,
                        "smoothie": smoothie,
                        "animal": animal,
                        "nationality": nat
                    }
                    new_houses = houses.copy()
                    new_houses[i] = candidate
                    if not is_valid_partial(new_houses, i):
                        continue
                    new_names = names.copy()
                    new_names.remove(name)
                    new_smoothies = smoothies.copy()
                    new_smoothies.remove(smoothie)
                    new_animals = animals.copy()
                    new_animals.remove(animal)
                    new_nationalities = nationalities.copy()
                    new_nationalities.remove(nat)
                    yield from backtrack(i+1, new_houses, new_names, new_smoothies, new_animals, new_nationalities)

def solve():
    names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
    smoothies = ["lime", "dragonfruit", "desert", "watermelon", "cherry"]
    animals = ["horse", "dog", "bird", "fish", "cat"]
    nationalities = ["german", "swede", "norwegian", "brit", "dane"]
    houses = [None] * 5
    for sol in backtrack(0, houses, names, smoothies, animals, nationalities):
        return sol
    return None

if __name__ == "__main__":
    sol = solve()
    if sol is not None:
        header = ["House", "Name", "smoothie", "animal", "nationality"]
        rows = []
        for house in sol:
            row = [
                house["House"],
                house["Name"],
                house["smoothie"],
                house["animal"],
                house["nationality"]
            ]
            rows.append(row)
        output = {"solution": {"header": header, "rows": rows}}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"solution": None}))