import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Eric", "Peter", "Arnold", "Bob", "Alice"]
    house_styles = ["modern", "craftsman", "ranch", "victorian", "colonial"]
    mothers = ["Penny", "Kailyn", "Holly", "Janelle", "Aniya"]
    phone_models = ["oneplus 9", "google pixel 6", "huawei p50", "iphone 13", "samsung galaxy s21"]
    drinks = ["coffee", "water", "root beer", "tea", "milk"]
    animals = ["fish", "dog", "horse", "bird", "cat"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for style_perm in itertools.permutations(house_styles):
            for mother_perm in itertools.permutations(mothers):
                for phone_perm in itertools.permutations(phone_models):
                    for drink_perm in itertools.permutations(drinks):
                        for animal_perm in itertools.permutations(animals):
                            # Check all constraints
                            if (
                                # 1. The person who uses a Google Pixel 6 is not in the first house.
                                phone_perm[0] != "google pixel 6" and
                                # 2. The one who only drinks water is Alice.
                                drink_perm[name_perm.index("Alice")] == "water" and
                                # 3. The person living in a colonial-style house is somewhere to the right of the person who uses a Huawei P50.
                                style_perm.index("colonial") > phone_perm.index("huawei p50") and
                                # 4. The person who keeps horses is the person who uses a OnePlus 9.
                                animal_perm[phone_perm.index("oneplus 9")] == "horse" and
                                # 5. The person in a ranch-style home is The person whose mother's name is Kailyn.
                                style_perm[mother_perm.index("Kailyn")] == "ranch" and
                                # 6. The root beer lover is the cat lover.
                                drink_perm[animal_perm.index("cat")] == "root beer" and
                                # 7. The person living in a colonial-style house is not in the fourth house.
                                style_perm[3] != "colonial" and
                                # 8. The bird keeper is in the fourth house.
                                animal_perm[3] == "bird" and
                                # 9. The tea drinker is Bob.
                                drink_perm[name_perm.index("Bob")] == "tea" and
                                # 10. The tea drinker is somewhere to the right of The person whose mother's name is Kailyn.
                                drink_perm.index("tea") > mother_perm.index("Kailyn") and
                                # 11. The root beer lover is somewhere to the left of The person whose mother's name is Kailyn.
                                drink_perm.index("root beer") < mother_perm.index("Kailyn") and
                                # 12. The person who keeps horses is the person in a modern-style house.
                                style_perm[animal_perm.index("horse")] == "modern" and
                                # 13. The person who uses an iPhone 13 is the person who likes milk.
                                phone_perm[drink_perm.index("milk")] == "iphone 13" and
                                # 14. The dog owner is the person who likes milk.
                                animal_perm[drink_perm.index("milk")] == "dog" and
                                # 15. The person who uses a Google Pixel 6 is the person in a Craftsman-style house.
                                style_perm[phone_perm.index("google pixel 6")] == "craftsman" and
                                # 16. Eric is not in the second house.
                                name_perm[1] != "Eric" and
                                # 17. The tea drinker is in the fourth house.
                                drink_perm[3] == "tea" and
                                # 18. The person who keeps horses is in the third house.
                                animal_perm[2] == "horse" and
                                # 19. The person in a modern-style house is The person whose mother's name is Penny.
                                mother_perm[style_perm.index("modern")] == "Penny" and
                                # 20. The root beer lover is Peter.
                                name_perm[drink_perm.index("root beer")] == "Peter" and
                                # 21. The person whose mother's name is Aniya is not in the fourth house.
                                mother_perm[3] != "Aniya" and
                                # 22. The person whose mother's name is Janelle is the one who only drinks water.
                                mother_perm[drink_perm.index("water")] == "Janelle"
                            ):
                                # If all constraints are satisfied, construct the solution
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"],
                                        "rows": [
                                            [str(h), name_perm[h-1], style_perm[h-1], mother_perm[h-1], phone_perm[h-1], drink_perm[h-1], animal_perm[h-1]]
                                            for h in houses
                                        ]
                                    }
                                }
                                return json.dumps(solution, indent=2)

# Output the solution
print(solve_puzzle())