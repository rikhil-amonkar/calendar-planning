import json
from constraint import Problem, AllDifferentConstraint

def var_name(category, value):
    return f"{category}_{value.replace(' ', '_').lower()}"

def add_same_house(problem, cat1, val1, cat2, val2):
    problem.addConstraint(lambda a, b: a == b, [var_name(cat1, val1), var_name(cat2, val2)])

def main():
    houses = [1, 2, 3]

    # Domains
    Names = ["Peter", "Arnold", "Eric"]
    BookGenres = ["science fiction", "mystery", "romance"]
    Smoothies = ["watermelon", "desert", "cherry"]
    Birthdays = ["april", "jan", "sept"]
    Heights = ["average", "very short", "short"]

    problem = Problem()

    # Add variables
    for n in Names:
        problem.addVariable(var_name("Name", n), houses)
    for g in BookGenres:
        problem.addVariable(var_name("BookGenre", g), houses)
    for s in Smoothies:
        problem.addVariable(var_name("Smoothie", s), houses)
    for b in Birthdays:
        problem.addVariable(var_name("Birthday", b), houses)
    for h in Heights:
        problem.addVariable(var_name("Height", h), houses)

    # AllDifferent constraints within each category
    problem.addConstraint(AllDifferentConstraint(), [var_name("Name", n) for n in Names])
    problem.addConstraint(AllDifferentConstraint(), [var_name("BookGenre", g) for g in BookGenres])
    problem.addConstraint(AllDifferentConstraint(), [var_name("Smoothie", s) for s in Smoothies])
    problem.addConstraint(AllDifferentConstraint(), [var_name("Birthday", b) for b in Birthdays])
    problem.addConstraint(AllDifferentConstraint(), [var_name("Height", h) for h in Heights])

    # Clues:
    # 1. The person who likes Cherry smoothies is not in the second house.
    problem.addConstraint(lambda x: x != 2, [var_name("Smoothie", "cherry")])

    # 2. Arnold is the person who loves mystery books.
    add_same_house(problem, "Name", "Arnold", "BookGenre", "mystery")

    # 3. The person whose birthday is in January is not in the first house.
    problem.addConstraint(lambda x: x != 1, [var_name("Birthday", "jan")])

    # 4. The person who is very short is the person who loves romance books.
    add_same_house(problem, "Height", "very short", "BookGenre", "romance")

    # 5. The person who loves mystery books is the person whose birthday is in September.
    add_same_house(problem, "BookGenre", "mystery", "Birthday", "sept")

    # 6. The person who has an average height is the Desert smoothie lover.
    add_same_house(problem, "Height", "average", "Smoothie", "desert")

    # 7. Eric is in the first house.
    problem.addConstraint(lambda x: x == 1, [var_name("Name", "Eric")])

    # 8. The Watermelon smoothie lover is the person who is short.
    add_same_house(problem, "Smoothie", "watermelon", "Height", "short")

    # 9. The Watermelon smoothie lover is Eric.
    add_same_house(problem, "Smoothie", "watermelon", "Name", "Eric")

    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"solution": {"header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"], "rows": []}}))
        return

    # Build rows for each house
    rows = []
    for house in [1, 2, 3]:
        name = next(n for n in Names if solution[var_name("Name", n)] == house)
        genre = next(g for g in BookGenres if solution[var_name("BookGenre", g)] == house)
        smoothie = next(s for s in Smoothies if solution[var_name("Smoothie", s)] == house)
        birthday = next(b for b in Birthdays if solution[var_name("Birthday", b)] == house)
        height = next(h for h in Heights if solution[var_name("Height", h)] == house)
        rows.append([str(house), name, genre, smoothie, birthday, height])

    output = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()