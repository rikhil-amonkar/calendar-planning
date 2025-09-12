from z3 import *
import json

# Problem parameters
houses = 5  # Example value; adjust based on your problem
names = [Const(f"name_{i}", StringSort()) for i in range(houses)]
musics = [Const(f"music_{i}", StringSort()) for i in range(houses)]
childrens = [Int(f"children_{i}") for i in range(houses)]
books = [Const(f"book_{i}", StringSort()) for i in range(houses)]

# Solver initialization
s = Solver()

# Add constraints (example constraints; replace with your actual logic)
for i in range(houses):
    s.add(Distinct([names[i], musics[i], books[i]]))  # Example uniqueness constraint
    s.add(childrens[i] >= 0)  # Example range constraint

# Add additional problem-specific constraints here...

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    rows = []
    for i in range(houses):
        house_num = str(i + 1)
        name_val = model.evaluate(names[i]).decl().name()
        music_val = model.evaluate(musics[i]).decl().name()
        child_val = model.evaluate(childrens[i]).as_string()
        book_val = model.evaluate(books[i]).decl().name()
        rows.append([house_num, name_val, music_val, child_val, book_val])
    solution = {
        "solution": {
            "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")