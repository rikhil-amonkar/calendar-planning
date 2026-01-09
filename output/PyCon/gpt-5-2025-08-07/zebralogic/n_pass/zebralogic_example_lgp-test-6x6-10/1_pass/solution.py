import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = range(1, 7)

    names = ['Arnold', 'Bob', 'Peter', 'Alice', 'Carol', 'Eric']
    foods = ['stew', 'grilled cheese', 'stir fry', 'soup', 'pizza', 'spaghetti']
    heights = ['tall', 'average', 'super tall', 'very short', 'very tall', 'short']
    drinks = ['root beer', 'boba tea', 'coffee', 'water', 'tea', 'milk']
    pets = ['hamster', 'fish', 'cat', 'dog', 'bird', 'rabbit']
    phones = ['samsung galaxy s21', 'xiaomi mi 11', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9']

    def var_name(category, value):
        return f"{category}_{value}"

    problem = Problem()

    # Add variables for each attribute value: each maps to a house number 1..6
    for n in names:
        problem.addVariable(var_name("Name", n), houses)
    for f in foods:
        problem.addVariable(var_name("Food", f), houses)
    for h in heights:
        problem.addVariable(var_name("Height", h), houses)
    for d in drinks:
        problem.addVariable(var_name("Drink", d), houses)
    for p in pets:
        problem.addVariable(var_name("Pet", p), houses)
    for ph in phones:
        problem.addVariable(var_name("Phone", ph), houses)

    # AllDifferent constraints within each category
    problem.addConstraint(AllDifferentConstraint(), [var_name("Name", n) for n in names])
    problem.addConstraint(AllDifferentConstraint(), [var_name("Food", f) for f in foods])
    problem.addConstraint(AllDifferentConstraint(), [var_name("Height", h) for h in heights])
    problem.addConstraint(AllDifferentConstraint(), [var_name("Drink", d) for d in drinks])
    problem.addConstraint(AllDifferentConstraint(), [var_name("Pet", p) for p in pets])
    problem.addConstraint(AllDifferentConstraint(), [var_name("Phone", ph) for ph in phones])

    V = var_name

    # Clues translated into constraints

    # 1. The person who uses an iPhone 13 is in the third house.
    problem.addConstraint(lambda x: x == 3, [V("Phone", "iphone 13")])

    # 2. Bob is the person who is tall.
    problem.addConstraint(lambda a, b: a == b, [V("Name", "Bob"), V("Height", "tall")])

    # 3. The person who loves the soup is in the second house.
    problem.addConstraint(lambda x: x == 2, [V("Food", "soup")])

    # 4. The root beer lover is directly left of the person who uses a Xiaomi Mi 11.
    problem.addConstraint(lambda a, b: a == b - 1, [V("Drink", "root beer"), V("Phone", "xiaomi mi 11")])

    # 5. The person who uses a Huawei P50 is directly left of the person who loves eating grilled cheese.
    problem.addConstraint(lambda a, b: a == b - 1, [V("Phone", "huawei p50"), V("Food", "grilled cheese")])

    # 6. The person who loves stir fry is the person who likes milk.
    problem.addConstraint(lambda a, b: a == b, [V("Food", "stir fry"), V("Drink", "milk")])

    # 7. The person who loves eating grilled cheese is the person who is tall.
    problem.addConstraint(lambda a, b: a == b, [V("Food", "grilled cheese"), V("Height", "tall")])

    # 8. The person who uses a Xiaomi Mi 11 is the coffee drinker.
    problem.addConstraint(lambda a, b: a == b, [V("Phone", "xiaomi mi 11"), V("Drink", "coffee")])

    # 9. The person who uses a OnePlus 9 is Arnold.
    problem.addConstraint(lambda a, b: a == b, [V("Phone", "oneplus 9"), V("Name", "Arnold")])

    # 10. The person who owns a rabbit is not in the fifth house.
    problem.addConstraint(lambda x: x != 5, [V("Pet", "rabbit")])

    # 11. The person with a pet hamster is somewhere to the right of the person who uses a Google Pixel 6.
    problem.addConstraint(lambda a, b: a > b, [V("Pet", "hamster"), V("Phone", "google pixel 6")])

    # 12. The person who is super tall is the person with an aquarium of fish.
    problem.addConstraint(lambda a, b: a == b, [V("Height", "super tall"), V("Pet", "fish")])

    # 13. The person with an aquarium of fish is Alice.
    problem.addConstraint(lambda a, b: a == b, [V("Pet", "fish"), V("Name", "Alice")])

    # 14. The tea drinker is directly left of the person who is a pizza lover.
    problem.addConstraint(lambda a, b: a == b - 1, [V("Drink", "tea"), V("Food", "pizza")])

    # 15. The person who uses a Samsung Galaxy S21 is Carol.
    problem.addConstraint(lambda a, b: a == b, [V("Phone", "samsung galaxy s21"), V("Name", "Carol")])

    # 16. The person who is a pizza lover is the person who is short.
    problem.addConstraint(lambda a, b: a == b, [V("Food", "pizza"), V("Height", "short")])

    # 17. Arnold is the person who is very tall.
    problem.addConstraint(lambda a, b: a == b, [V("Name", "Arnold"), V("Height", "very tall")])

    # 18. The spaghetti eater uses a Google Pixel 6.
    problem.addConstraint(lambda a, b: a == b, [V("Food", "spaghetti"), V("Phone", "google pixel 6")])

    # 19. The boba tea drinker is somewhere to the right of the person who loves the soup.
    problem.addConstraint(lambda a, b: a > b, [V("Drink", "boba tea"), V("Food", "soup")])

    # 20. The person with a pet hamster is not in the fifth house.
    problem.addConstraint(lambda x: x != 5, [V("Pet", "hamster")])

    # 21. The person who is very tall is not in the second house.
    problem.addConstraint(lambda x: x != 2, [V("Height", "very tall")])

    # 22. The person who is super tall is somewhere to the left of Peter.
    problem.addConstraint(lambda a, b: a < b, [V("Height", "super tall"), V("Name", "Peter")])

    # 23. The person who is very short is the person who loves the spaghetti eater. (Interpretation: very short person eats spaghetti)
    problem.addConstraint(lambda a, b: a == b, [V("Height", "very short"), V("Food", "spaghetti")])

    # 24. The person who keeps a pet bird is somewhere to the left of the person who loves the spaghetti eater.
    problem.addConstraint(lambda a, b: a < b, [V("Pet", "bird"), V("Food", "spaghetti")])

    # 25. The person with an aquarium of fish is directly left of Eric.
    problem.addConstraint(lambda a, b: a == b - 1, [V("Pet", "fish"), V("Name", "Eric")])

    # 26. The person who owns a dog is the person who likes milk.
    problem.addConstraint(lambda a, b: a == b, [V("Pet", "dog"), V("Drink", "milk")])

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found")

    sol = solutions[0]

    def value_at_house(category, values_list, house):
        for val in values_list:
            if sol[V(category, val)] == house:
                return val
        return None

    header = ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"]
    rows = []
    for h in range(1, 7):
        row = [
            str(h),
            value_at_house("Name", names, h),
            value_at_house("Food", foods, h),
            value_at_house("Height", heights, h),
            value_at_house("Drink", drinks, h),
            value_at_house("Pet", pets, h),
            value_at_house("Phone", phones, h),
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()