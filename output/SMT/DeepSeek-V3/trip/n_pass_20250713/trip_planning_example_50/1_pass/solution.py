from z3 import *

def solve_with_z3():
    s = Solver()

    a = Int('a')
    b = Int('b')

    s.add(a >= 1)
    s.add(b > a)
    s.add(b <= 12)

    s.add(a == 4)
    s.add((b - a + 1) == 3)
    s.add((12 - b + 1) == 7)

    if s.check() == sat:
        m = s.model()
        a_val = m[a].as_long()
        b_val = m[b].as_long()

        itinerary = [
            {"day_range": f"Day 1-{a_val}", "place": "Vilnius"},
            {"day_range": f"Day {a_val}", "place": "Vilnius"},
            {"day_range": f"Day {a_val}", "place": "Munich"},
            {"day_range": f"Day {a_val}-{b_val}", "place": "Munich"},
            {"day_range": f"Day {b_val}", "place": "Munich"},
            {"day_range": f"Day {b_val}", "place": "Mykonos"},
            {"day_range": f"Day {b_val}-12", "place": "Mykonos"}
        ]
        return {"itinerary": itinerary}
    else:
        return {"error": "No solution found"}

result = solve_with_z3()
print(result)