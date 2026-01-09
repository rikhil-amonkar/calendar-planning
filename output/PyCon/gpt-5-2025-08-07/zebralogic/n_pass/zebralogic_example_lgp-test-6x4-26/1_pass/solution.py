import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = range(1, 7)

    names = ["Peter", "Bob", "Carol", "Eric", "Alice", "Arnold"]
    pets = ["bird", "dog", "cat", "rabbit", "fish", "hamster"]
    styles = ["victorian", "ranch", "modern", "mediterranean", "colonial", "craftsman"]
    birthdays = ["mar", "sept", "may", "feb", "jan", "april"]

    problem = Problem()

    # Add variables with domains
    for n in names:
        problem.addVariable(n, houses)
    for p in pets:
        problem.addVariable(p, houses)
    for s in styles:
        problem.addVariable(s, houses)
    for b in birthdays:
        problem.addVariable(b, houses)

    # All-different constraints per category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), pets)
    problem.addConstraint(AllDifferentConstraint(), styles)
    problem.addConstraint(AllDifferentConstraint(), birthdays)

    # Clues
    # 1. Hamster right of March
    problem.addConstraint(lambda h, m: h > m, ["hamster", "mar"])

    # 2. January left of September
    problem.addConstraint(lambda j, s: j < s, ["jan", "sept"])

    # 3. May is in the second house
    problem.addConstraint(lambda x: x == 2, ["may"])

    # 4. Colonial is in the second house
    problem.addConstraint(lambda x: x == 2, ["colonial"])

    # 5. Carol is in the third house
    problem.addConstraint(lambda x: x == 3, ["Carol"])

    # 6. Mediterranean not in the sixth house
    problem.addConstraint(lambda x: x != 6, ["mediterranean"])

    # 7. Fish is to the right of Bob
    problem.addConstraint(lambda f, b: f > b, ["fish", "Bob"])

    # 8. Eric is in the sixth house
    problem.addConstraint(lambda x: x == 6, ["Eric"])

    # 9. One house between cat and victorian (distance 2)
    problem.addConstraint(lambda c, v: abs(c - v) == 2, ["cat", "victorian"])

    # 10. Two houses between victorian and hamster (distance 3)
    problem.addConstraint(lambda v, h: abs(v - h) == 3, ["victorian", "hamster"])

    # 11. Craftsman is Arnold
    problem.addConstraint(lambda a, c: a == c, ["Arnold", "craftsman"])

    # 12. Colonial left of modern
    problem.addConstraint(lambda c, m: c < m, ["colonial", "modern"])

    # 13. Fish not in the second house
    problem.addConstraint(lambda f: f != 2, ["fish"])

    # 14. Peter is colonial
    problem.addConstraint(lambda p, c: p == c, ["Peter", "colonial"])

    # 15. January directly left of April
    problem.addConstraint(lambda j, a: a - j == 1, ["jan", "april"])

    # 16. One house between bird and modern (distance 2)
    problem.addConstraint(lambda b, m: abs(b - m) == 2, ["bird", "modern"])

    # 17. Carol is March
    problem.addConstraint(lambda c, m: c == m, ["Carol", "mar"])

    # 18. Craftsman is in the fourth house
    problem.addConstraint(lambda x: x == 4, ["craftsman"])

    # 19. Dog is in the fourth house
    problem.addConstraint(lambda x: x == 4, ["dog"])

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found")

    sol = solutions[0]

    # Build output rows by house index
    header = ["House", "Name", "Pet", "HouseStyle", "Birthday"]
    rows = []
    for h in range(1, 7):
        # Find entries matching house h
        name = next(n for n in names if sol[n] == h)
        pet = next(p for p in pets if sol[p] == h)
        style = next(s for s in styles if sol[s] == h)
        bday = next(b for b in birthdays if sol[b] == h)
        rows.append([str(h), name, pet, style, bday])

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))