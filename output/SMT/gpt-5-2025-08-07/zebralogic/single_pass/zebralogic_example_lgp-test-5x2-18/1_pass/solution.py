from z3 import Solver, Int, Distinct, And, Or, If, Sum, Abs
import json

def solve():
    # Domain definitions
    HOUSES = list(range(5))  # indices 0..4 correspond to houses 1..5

    NAMES = ["Eric", "Alice", "Peter", "Bob", "Arnold"]
    CHILDREN = ["Timothy", "Meredith", "Samantha", "Fred", "Bella"]

    # Indices for readability
    ERIC, ALICE, PETER, BOB, ARNOLD = range(5)
    TIMOTHY, MEREDITH, SAMANTHA, FRED, BELLA = range(5)

    # Variables: for each house, which name and which child
    Name = [Int(f"name_{i+1}") for i in HOUSES]
    Child = [Int(f"child_{i+1}") for i in HOUSES]

    s = Solver()

    # Domains
    for i in HOUSES:
        s.add(And(Name[i] >= 0, Name[i] < len(NAMES)))
        s.add(And(Child[i] >= 0, Child[i] < len(CHILDREN)))

    # All-different constraints
    s.add(Distinct(Name))
    s.add(Distinct(Child))

    # Helper to get the position (1..5) of a given value in a var list
    def pos_of(var_list, value_index):
        # Exactly one will match due to Distinct + full coverage
        return Sum([If(var_list[i] == value_index, i + 1, 0) for i in HOUSES])

    # Clues:
    # 1. Bob is somewhere to the left of the person's child named Samantha.
    s.add(pos_of(Name, BOB) < pos_of(Child, SAMANTHA))

    # 2. The person who is the mother of Timothy is somewhere to the left of Samantha.
    s.add(pos_of(Child, TIMOTHY) < pos_of(Child, SAMANTHA))

    # 3. Fred is in the second house.
    s.add(Child[1] == FRED)  # house index 1 => house 2

    # 4. There is one house between Alice and Samantha.
    s.add(Abs(pos_of(Name, ALICE) - pos_of(Child, SAMANTHA)) == 2)

    # 5. Eric is not in the third house.
    s.add(Name[2] != ERIC)  # house index 2 => house 3

    # 6. Bob is not in the third house.
    s.add(Name[2] != BOB)

    # 7. Fred is directly left of Bella.
    s.add(pos_of(Child, FRED) + 1 == pos_of(Child, BELLA))

    # 8. Samantha is somewhere to the left of Peter.
    s.add(pos_of(Child, SAMANTHA) < pos_of(Name, PETER))

    if s.check() != 1:  # sat
        raise RuntimeError("No solution found")

    m = s.model()

    # Build solution rows
    rows = []
    for i in HOUSES:
        name_idx = m[Name[i]].as_long()
        child_idx = m[Child[i]].as_long()
        rows.append([str(i + 1), NAMES[name_idx], CHILDREN[child_idx]])

    output = {
        "solution": {
            "header": ["House", "Name", "Children"],
            "rows": rows
        }
    }

    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    solve()