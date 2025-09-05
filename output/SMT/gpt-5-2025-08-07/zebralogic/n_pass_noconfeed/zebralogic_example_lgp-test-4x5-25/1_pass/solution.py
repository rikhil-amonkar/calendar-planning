import json
from z3 import *

def main():
    # Houses are 1..4
    houses = [1, 2, 3, 4]

    # Attribute domains
    Names = ['Arnold', 'Peter', 'Eric', 'Alice']
    Styles = ['craftsman', 'colonial', 'victorian', 'ranch']
    Hairs = ['red', 'blonde', 'black', 'brown']
    Children = ['Bella', 'Fred', 'Meredith', 'Samantha']
    Books = ['mystery', 'fantasy', 'romance', 'science fiction']

    name_idx = {v: i for i, v in enumerate(Names)}
    style_idx = {v: i for i, v in enumerate(Styles)}
    hair_idx = {v: i for i, v in enumerate(Hairs)}
    child_idx = {v: i for i, v in enumerate(Children)}
    book_idx = {v: i for i, v in enumerate(Books)}

    # Variables: for each house, assign index of each category
    name = [Int(f"name_{h}") for h in houses]
    style = [Int(f"style_{h}") for h in houses]
    hair = [Int(f"hair_{h}") for h in houses]
    child = [Int(f"child_{h}") for h in houses]
    book = [Int(f"book_{h}") for h in houses]

    s = Solver()

    # Domain constraints
    for arr in [name, style, hair, child, book]:
        for v in arr:
            s.add(And(v >= 0, v < 4))

    # AllDifferent constraints across houses for each category
    s.add(Distinct(name))
    s.add(Distinct(style))
    s.add(Distinct(hair))
    s.add(Distinct(child))
    s.add(Distinct(book))

    # Clues encoded:

    # 1. The person in a Craftsman-style house is in the third house.
    s.add(style[3 - 1] == style_idx['craftsman'])

    # 2. Alice is the person who loves romance books.
    for i in range(4):
        s.add((name[i] == name_idx['Alice']) == (book[i] == book_idx['romance']))

    # 3. The person who has brown hair is in the fourth house.
    s.add(hair[4 - 1] == hair_idx['brown'])

    # 4. The person's child is named Samantha is in the fourth house.
    s.add(child[4 - 1] == child_idx['Samantha'])

    # 5. The person in a ranch-style home is somewhere to the right of the person who has red hair.
    ranch_right_of_red = []
    for i in houses:
        for j in houses:
            if i > j:
                ranch_right_of_red.append(And(style[i - 1] == style_idx['ranch'], hair[j - 1] == hair_idx['red']))
    s.add(Or(ranch_right_of_red))

    # 6. Peter is the person's child is named Bella. (Peter's child is Bella)
    for i in range(4):
        s.add((name[i] == name_idx['Peter']) == (child[i] == child_idx['Bella']))

    # 7. Arnold is the person who has red hair.
    for i in range(4):
        s.add((name[i] == name_idx['Arnold']) == (hair[i] == hair_idx['red']))

    # 8. Alice is the person living in a colonial-style house.
    for i in range(4):
        s.add((name[i] == name_idx['Alice']) == (style[i] == style_idx['colonial']))

    # 9. The person who has black hair is in the second house.
    s.add(hair[2 - 1] == hair_idx['black'])

    # 10. The person who loves fantasy books is Peter.
    for i in range(4):
        s.add((book[i] == book_idx['fantasy']) == (name[i] == name_idx['Peter']))

    # 11. Arnold is the person's child is named Meredith. (Arnold's child is Meredith)
    for i in range(4):
        s.add((name[i] == name_idx['Arnold']) == (child[i] == child_idx['Meredith']))

    # 12. The person who has black hair is Eric.
    for i in range(4):
        s.add((hair[i] == hair_idx['black']) == (name[i] == name_idx['Eric']))

    # 13. The person who loves science fiction books is Arnold.
    for i in range(4):
        s.add((book[i] == book_idx['science fiction']) == (name[i] == name_idx['Arnold']))

    if s.check() != sat:
        raise Exception("No solution found")

    m = s.model()

    # Build solution rows per house 1..4
    rows = []
    for h in houses:
        n = Names[m[name[h - 1]].as_long()]
        st = Styles[m[style[h - 1]].as_long()]
        hr = Hairs[m[hair[h - 1]].as_long()]
        ch = Children[m[child[h - 1]].as_long()]
        bk = Books[m[book[h - 1]].as_long()]
        rows.append([str(h), n, st, hr, ch, bk])

    output = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()