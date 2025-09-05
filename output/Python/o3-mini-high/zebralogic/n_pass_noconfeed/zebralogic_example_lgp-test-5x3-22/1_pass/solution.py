import itertools
import json

def main():
    names_all = ["Arnold", "Eric", "Bob", "Peter", "Alice"]
    smoothies_all = ["desert", "watermelon", "lime", "cherry", "dragonfruit"]
    nationalities_all = ["german", "swede", "norwegian", "dane", "brit"]

    solution = None

    for names in itertools.permutations(names_all):
        # Constraint: Alice is in the third house.
        if names[2] != "Alice":
            continue
        # Constraint: Peter is not in the first house.
        if names[0] == "Peter":
            continue

        for smoothies in itertools.permutations(smoothies_all):
            # Constraint: The Dragonfruit smoothie lover is in the second house.
            if smoothies[1] != "dragonfruit":
                continue
            # Constraint: The Watermelon smoothie lover is in the third house.
            if smoothies[2] != "watermelon":
                continue
            # Constraint: The Desert smoothie lover is not in the fifth house.
            if smoothies[4] == "desert":
                continue

            for nationalities in itertools.permutations(nationalities_all):
                # Constraint: Alice is the Norwegian. (She is in the third house.)
                if nationalities[2] != "norwegian":
                    continue
                # Constraint: The Swedish person is somewhere to the left of the Dragonfruit smoothie lover.
                # With Dragonfruit fixed in house 2, Swedish must be in house 1.
                if nationalities[0] != "swede":
                    continue

                # Constraint: The Dragonfruit smoothie lover (house 2) is to the left of Eric.
                if names.index("Eric") <= 1:
                    continue

                # Constraint: Bob is the Dane.
                if names.index("Bob") != nationalities.index("dane"):
                    continue

                # Constraint: There are two houses between the person who drinks Lime smoothies and the Dane.
                if abs(smoothies.index("lime") - nationalities.index("dane")) != 3:
                    continue

                # Constraint: The Dane and the British person are next to each other.
                if abs(nationalities.index("dane") - nationalities.index("brit")) != 1:
                    continue

                # All constraints satisfied, record the solution.
                houses = []
                for i in range(5):
                    house = [str(i+1), names[i], smoothies[i], nationalities[i]]
                    houses.append(house)
                solution = houses
                break
            if solution:
                break
        if solution:
            break

    result = {"solution": {"header": ["House", "Name", "Smoothie", "Nationality"],
                             "rows": solution if solution is not None else []}}
    print(json.dumps(result))

if __name__ == "__main__":
    main()