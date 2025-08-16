import json
from z3 import *

def main():
    name1 = String('name1')
    name2 = String('name2')
    genre1 = String('genre1')
    genre2 = String('genre2')

    solver = Solver()

    # Name constraints
    solver.add(Or(name1 == "Eric", name1 == "Arnold"))
    solver.add(Or(name2 == "Eric", name2 == "Arnold"))
    solver.add(name1 != name2)

    # Genre constraints
    solver.add(Or(genre1 == "science fiction", genre1 == "mystery"))
    solver.add(Or(genre2 == "science fiction", genre2 == "mystery"))
    solver.add(genre1 != genre2)

    # Clue constraints
    solver.add(name1 == "Eric")
    solver.add(genre2 == "mystery")

    if solver.check() == sat:
        model = solver.model()
        n1 = model[name1]
        n2 = model[name2]
        g1 = model[genre1]
        g2 = model[genre2]

        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre"],
                "rows": [
                    ["1", n1, g1],
                    ["2", n2, g2]
                ]
            }
        }

        print(json.dumps(solution))

if __name__ == "__main__":
    main()