import json
from z3 import *

def solve_puzzle():
    # Define enums for names and heights
    names, (Arnold, Peter, Eric) = EnumSort('Names', ['Arnold', 'Peter', 'Eric'])
    heights, (short, average, very_short) = EnumSort('Heights', ['short', 'average', 'very_short'])

    # Variables for each house
    n1, n2, n3 = Consts('n1 n2 n3', names)
    h1, h2, h3 = Consts('h1 h2 h3', heights)

    s = Solver()

    # All names and heights are distinct
    s.add(Distinct(n1, n2, n3))
    s.add(Distinct(h1, h2, h3))

    # Clue 2: Short is in house 1
    s.add(h1 == short)

    # Clue 3: One house between short (house 1) and very_short => very_short in house 3
    s.add(h3 == very_short)

    # Clue 4: Arnold is next to very_short (house 3), so Arnold is in house 2
    s.add(n2 == Arnold)

    # Clue 1: Peter is to the right of Eric
    s.add(Implies(n1 == Eric, Or(n2 == Peter, n3 == Peter)))
    s.add(Implies(n2 == Eric, n3 == Peter))
    s.add(n3 != Eric)

    if s.check() == sat:
        model = s.model()
        # Extract values
        name1 = model[n1].as_string()
        name2 = model[n2].as_string()
        name3 = model[n3].as_string()

        h1_val = model[h1].as_string()
        h2_val = model[h2].as_string()
        h3_val = model[h3].as_string()

        # Convert 'very_short' to 'very short' for output
        def process_height(h):
            return 'very short' if h == 'very_short' else h

        h1_val = process_height(h1_val)
        h2_val = process_height(h2_val)
        h3_val = process_height(h3_val)

        solution = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": [
                    ["1", name1, h1_val],
                    ["2", name2, h2_val],
                    ["3", name3, h3_val]
                ]
            }
        }

        return json.dumps(solution, indent=2)
    else:
        return json.dumps({"error": "No solution found"})

# Output the solution as JSON
print(solve_puzzle())