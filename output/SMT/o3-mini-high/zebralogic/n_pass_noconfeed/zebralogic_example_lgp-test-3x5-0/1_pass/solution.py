import json
from z3 import Solver, Int, Distinct, Implies, And

def main():
    s = Solver()

    # There are 3 houses (0,1,2 corresponding to houses 1,2,3)
    houses = range(3)
    # Define variables for each house attribute. Their values will be in {0,1,2}.
    # Names: 0: "Peter", 1: "Arnold", 2: "Eric"
    name_vars = [Int(f"name_{i}") for i in houses]
    # BookGenre: 0: "science fiction", 1: "mystery", 2: "romance"
    book_vars = [Int(f"book_{i}") for i in houses]
    # Smoothie: 0: "watermelon", 1: "desert", 2: "cherry"
    smoothie_vars = [Int(f"smoothie_{i}") for i in houses]
    # Birthday: 0: "april", 1: "jan", 2: "sept"
    birthday_vars = [Int(f"birthday_{i}") for i in houses]
    # Height: 0: "average", 1: "very short", 2: "short"
    height_vars = [Int(f"height_{i}") for i in houses]

    # Domain constraints: each variable is between 0 and 2.
    for var in name_vars + book_vars + smoothie_vars + birthday_vars + height_vars:
        s.add(var >= 0, var <= 2)

    # All-different constraints for each category.
    s.add(Distinct(name_vars))
    s.add(Distinct(book_vars))
    s.add(Distinct(smoothie_vars))
    s.add(Distinct(birthday_vars))
    s.add(Distinct(height_vars))

    # Clue 1: The person who likes Cherry smoothies is not in the second house (house index 1).
    # Cherry smoothie is mapped to 2.
    s.add(smoothie_vars[1] != 2)

    # Clue 2: Arnold is the person who loves mystery books.
    # Arnold is represented by 1 (in names) and mystery is represented by 1 (in books).
    for i in houses:
        s.add(Implies(name_vars[i] == 1, book_vars[i] == 1))

    # Clue 3: The person whose birthday is in January is not in the first house (house index 0).
    # January is mapped to 1 in birthdays.
    s.add(birthday_vars[0] != 1)

    # Clue 4: The person who is very short is the person who loves romance books.
    # Very short in heights is 1, romance in books is 2.
    for i in houses:
        s.add(And(Implies(height_vars[i] == 1, book_vars[i] == 2),
                  Implies(book_vars[i] == 2, height_vars[i] == 1)))

    # Clue 5: The person who loves mystery books is the person whose birthday is in September.
    # Mystery in books is 1 and September in birthdays is 2.
    for i in houses:
        s.add(And(Implies(book_vars[i] == 1, birthday_vars[i] == 2),
                  Implies(birthday_vars[i] == 2, book_vars[i] == 1)))

    # Clue 6: The person who has an average height is the Desert smoothie lover.
    # Average in heights is 0 and desert in smoothies is 1.
    for i in houses:
        s.add(And(Implies(height_vars[i] == 0, smoothie_vars[i] == 1),
                  Implies(smoothie_vars[i] == 1, height_vars[i] == 0)))

    # Clue 7: Eric is in the first house (house index 0).
    # Eric is represented by 2.
    s.add(name_vars[0] == 2)

    # Clue 8: The Watermelon smoothie lover is the person who is short.
    # Watermelon in smoothies is 0 and short in heights is 2.
    for i in houses:
        s.add(And(Implies(smoothie_vars[i] == 0, height_vars[i] == 2),
                  Implies(height_vars[i] == 2, smoothie_vars[i] == 0)))

    # Clue 9: The Watermelon smoothie lover is Eric.
    # For the house where the name is Eric (2), the smoothie must be watermelon (0).
    for i in houses:
        s.add(Implies(name_vars[i] == 2, smoothie_vars[i] == 0))

    if s.check() == "sat" or s.check() == True:
        m = s.model()
        # Mapping dictionaries.
        names_map = {0: "Peter", 1: "Arnold", 2: "Eric"}
        books_map = {0: "science fiction", 1: "mystery", 2: "romance"}
        smoothies_map = {0: "watermelon", 1: "desert", 2: "cherry"}
        birthdays_map = {0: "april", 1: "jan", 2: "sept"}
        heights_map = {0: "average", 1: "very short", 2: "short"}

        rows = []
        for i in houses:
            house_num = str(i + 1)
            name_str = names_map[m.evaluate(name_vars[i]).as_long()]
            book_str = books_map[m.evaluate(book_vars[i]).as_long()]
            smoothie_str = smoothies_map[m.evaluate(smoothie_vars[i]).as_long()]
            birthday_str = birthdays_map[m.evaluate(birthday_vars[i]).as_long()]
            height_str = heights_map[m.evaluate(height_vars[i]).as_long()]
            rows.append([house_num, name_str, book_str, smoothie_str, birthday_str, height_str])

        output = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
                "rows": rows
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == '__main__':
    main()