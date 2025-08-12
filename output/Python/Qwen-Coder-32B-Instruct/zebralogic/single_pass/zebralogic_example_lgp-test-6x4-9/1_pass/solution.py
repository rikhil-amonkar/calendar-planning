import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Carol", "Bob", "Alice", "Arnold", "Eric", "Peter"]
    phones = ["samsung galaxy s21", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9", "xiaomi mi 11"]
    nationalities = ["swede", "chinese", "norwegian", "dane", "german", "brit"]
    colors = ["blue", "red", "yellow", "green", "white", "purple"]

    # Generate all possible permutations
    all_permutations = list(itertools.permutations(range(6)))

    def is_valid(permutation):
        name_order = permutation[0]
        phone_order = permutation[1]
        nationality_order = permutation[2]
        color_order = permutation[3]

        # Clue 1: Carol is not in the third house.
        if name_order.index(names.index("Carol")) == 2:
            return False

        # Clue 2: There is one house between the Dane and the British person.
        if abs(nationality_order.index(nationalities.index("dane")) - nationality_order.index(nationalities.index("brit"))) != 2:
            return False

        # Clue 3: Carol is the person whose favorite color is green.
        if name_order.index(names.index("Carol")) != color_order.index(colors.index("green")):
            return False

        # Clue 4: Arnold is directly left of Alice.
        if name_order.index(names.index("Arnold")) + 1 != name_order.index(names.index("Alice")):
            return False

        # Clue 5: Alice is the German.
        if name_order.index(names.index("Alice")) != nationality_order.index(nationalities.index("german")):
            return False

        # Clue 6: The person who uses a OnePlus 9 is the person who loves purple.
        if phone_order.index(phones.index("oneplus 9")) != color_order.index(colors.index("purple")):
            return False

        # Clue 7: The person who uses a Huawei P50 is not in the third house.
        if phone_order.index(phones.index("huawei p50")) == 2:
            return False

        # Clue 8: The person who uses a Samsung Galaxy S21 is in the fifth house.
        if phone_order.index(phones.index("samsung galaxy s21")) != 4:
            return False

        # Clue 9: The person who loves white is somewhere to the right of the person whose favorite color is red.
        if color_order.index(colors.index("white")) < color_order.index(colors.index("red")):
            return False

        # Clue 10: The person who uses a Samsung Galaxy S21 is Bob.
        if phone_order.index(phones.index("samsung galaxy s21")) != name_order.index(names.index("Bob")):
            return False

        # Clue 11: The Dane is the person who loves yellow.
        if nationality_order.index(nationalities.index("dane")) != color_order.index(colors.index("yellow")):
            return False

        # Clue 12: The person who uses a Samsung Galaxy S21 is somewhere to the left of Peter.
        if phone_order.index(phones.index("samsung galaxy s21")) > name_order.index(names.index("Peter")):
            return False

        # Clue 13: The person who loves blue is Peter.
        if color_order.index(colors.index("blue")) != name_order.index(names.index("Peter")):
            return False

        # Clue 14: Peter is the British person.
        if name_order.index(names.index("Peter")) != nationality_order.index(nationalities.index("brit")):
            return False

        # Clue 15: The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
        if phone_order.index(phones.index("samsung galaxy s21")) + 1 != phone_order.index(phones.index("iphone 13")):
            return False

        # Clue 16: The Norwegian is the person who loves purple.
        if nationality_order.index(nationalities.index("norwegian")) != color_order.index(colors.index("purple")):
            return False

        # Clue 17: The person who uses a Xiaomi Mi 11 is the Chinese.
        if phone_order.index(phones.index("xiaomi mi 11")) != nationality_order.index(nationalities.index("chinese")):
            return False

        return True

    for permutation in itertools.product(all_permutations, repeat=4):
        if is_valid(permutation):
            name_order, phone_order, nationality_order, color_order = permutation
            solution = []
            for house in range(6):
                name = names[name_order[house]]
                phone = phones[phone_order[house]]
                nationality = nationalities[nationality_order[house]]
                color = colors[color_order[house]]
                solution.append([str(house + 1), name, phone, nationality, color])
            return json.dumps({
                "solution": {
                    "header": ["House", "Name", "Phone Model", "Nationality", "Favorite Color"],
                    "rows": solution
                }
            }, indent=2)

print(solve_puzzle())