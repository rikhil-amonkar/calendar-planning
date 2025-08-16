import json
from z3 import Solver, Int, Distinct, Or

def solve_puzzle():
    houses = range(1, 6)

    names = ["Peter", "Alice", "Bob", "Eric", "Arnold"]
    heights = ["very tall", "average", "tall", "very short", "short"]

    house_of_name = {n: Int(f"house_name_{n}") for n in names}
    house_of_height = {h: Int(f"house_height_{h.replace(' ', '_')}") for h in heights}

    s = Solver()

    # Domain constraints
    for v in house_of_name.values():
        s.add(Or([v == i for i in houses]))
    for v in house_of_height.values():
        s.add(Or([v == i for i in houses]))

    # Uniqueness constraints
    s.add(Distinct(*house_of_name.values()))
    s.add(Distinct(*house_of_height.values()))

    # Clues:
    # 1. The person who is short is in the second house.
    s.add(house_of_height["short"] == 2)

    # 2. Peter is directly left of Bob.
    s.add(house_of_name["Peter"] + 1 == house_of_name["Bob"])

    # 3. Eric is somewhere to the left of Peter.
    s.add(house_of_name["Eric"] < house_of_name["Peter"])

    # 4. The person who is very tall is directly left of Peter.
    s.add(house_of_height["very tall"] + 1 == house_of_name["Peter"])

    # 5. Alice is directly left of the person who has an average height.
    s.add(house_of_name["Alice"] + 1 == house_of_height["average"])

    # 6. The person who is short and the person who is very short are next to each other.
    s.add(Or(house_of_height["short"] - house_of_height["very short"] == 1,
             house_of_height["very short"] - house_of_height["short"] == 1))

    # 7. The person who has an average height is in the fifth house.
    s.add(house_of_height["average"] == 5)

    if s.check() != 1:  # sat
        raise RuntimeError("No solution found")

    m = s.model()

    # Build mappings from house to attributes
    house_to_name = {}
    for n in names:
        h = m.eval(house_of_name[n]).as_long()
        house_to_name[h] = n

    house_to_height = {}
    for hgt in heights:
        h = m.eval(house_of_height[hgt]).as_long()
        house_to_height[h] = hgt

    rows = []
    for h in houses:
        rows.append([str(h), house_to_name[h], house_to_height[h]])

    result = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))