import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = range(1, 7)

    names = ["Carol", "Bob", "Alice", "Arnold", "Eric", "Peter"]
    phones = ["samsung galaxy s21", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9", "xiaomi mi 11"]
    nationalities = ["swede", "chinese", "norwegian", "dane", "german", "brit"]
    colors = ["blue", "red", "yellow", "green", "white", "purple"]

    problem = Problem()

    # Add variables for each attribute mapped to a house number
    for n in names:
        problem.addVariable(f"Name:{n}", houses)
    for p in phones:
        problem.addVariable(f"Phone:{p}", houses)
    for nat in nationalities:
        problem.addVariable(f"Nat:{nat}", houses)
    for c in colors:
        problem.addVariable(f"Color:{c}", houses)

    # All-different constraints for each category
    problem.addConstraint(AllDifferentConstraint(), [f"Name:{n}" for n in names])
    problem.addConstraint(AllDifferentConstraint(), [f"Phone:{p}" for p in phones])
    problem.addConstraint(AllDifferentConstraint(), [f"Nat:{nat}" for nat in nationalities])
    problem.addConstraint(AllDifferentConstraint(), [f"Color:{c}" for c in colors])

    # Clues as constraints

    # 1. Carol is not in the third house.
    problem.addConstraint(lambda x: x != 3, (f"Name:Carol",))

    # 2. There is one house between the Dane and the British person.
    problem.addConstraint(lambda d, b: abs(d - b) == 2, (f"Nat:dane", f"Nat:brit"))

    # 3. Carol is the person whose favorite color is green.
    problem.addConstraint(lambda a, b: a == b, (f"Name:Carol", f"Color:green"))

    # 4. Arnold is directly left of Alice.
    problem.addConstraint(lambda arn, ali: arn + 1 == ali, (f"Name:Arnold", f"Name:Alice"))

    # 5. Alice is the German.
    problem.addConstraint(lambda a, g: a == g, (f"Name:Alice", f"Nat:german"))

    # 6. The person who uses a OnePlus 9 is the person who loves purple.
    problem.addConstraint(lambda p, c: p == c, (f"Phone:oneplus 9", f"Color:purple"))

    # 7. The person who uses a Huawei P50 is not in the third house.
    problem.addConstraint(lambda x: x != 3, (f"Phone:huawei p50",))

    # 8. The person who uses a Samsung Galaxy S21 is in the fifth house.
    problem.addConstraint(lambda x: x == 5, (f"Phone:samsung galaxy s21",))

    # 9. The person who loves white is somewhere to the right of the person whose favorite color is red.
    problem.addConstraint(lambda w, r: w > r, (f"Color:white", f"Color:red"))

    # 10. The person who uses a Samsung Galaxy S21 is Bob.
    problem.addConstraint(lambda b, s: b == s, (f"Name:Bob", f"Phone:samsung galaxy s21"))

    # 11. The Dane is the person who loves yellow.
    problem.addConstraint(lambda d, y: d == y, (f"Nat:dane", f"Color:yellow"))

    # 12. The person who uses a Samsung Galaxy S21 is somewhere to the left of Peter.
    problem.addConstraint(lambda s, p: s < p, (f"Phone:samsung galaxy s21", f"Name:Peter"))

    # 13. The person who loves blue is Peter.
    problem.addConstraint(lambda b, p: b == p, (f"Color:blue", f"Name:Peter"))

    # 14. Peter is the British person.
    problem.addConstraint(lambda p, b: p == b, (f"Name:Peter", f"Nat:brit"))

    # 15. The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
    problem.addConstraint(lambda s, i: s + 1 == i, (f"Phone:samsung galaxy s21", f"Phone:iphone 13"))

    # 16. The Norwegian is the person who loves purple.
    problem.addConstraint(lambda n, p: n == p, (f"Nat:norwegian", f"Color:purple"))

    # 17. The person who uses a Xiaomi Mi 11 is the Chinese.
    problem.addConstraint(lambda x, c: x == c, (f"Phone:xiaomi mi 11", f"Nat:chinese"))

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found for the given puzzle.")

    sol = solutions[0]

    # Build rows for each house
    header = ["House", "Name", "PhoneModel", "Nationality", "Color"]
    rows = []
    for h in range(1, 7):
        # Find the attribute at house h
        name_at_h = next(n for n in names if sol[f"Name:{n}"] == h)
        phone_at_h = next(p for p in phones if sol[f"Phone:{p}"] == h)
        nat_at_h = next(nat for nat in nationalities if sol[f"Nat:{nat}"] == h)
        color_at_h = next(c for c in colors if sol[f"Color:{c}"] == h)
        rows.append([str(h), name_at_h, phone_at_h, nat_at_h, color_at_h])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()