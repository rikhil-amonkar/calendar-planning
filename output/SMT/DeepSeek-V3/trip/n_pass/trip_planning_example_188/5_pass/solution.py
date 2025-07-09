from z3 import *

def solve_itinerary():
    s = Solver()

    # Fixed Brussels stay (Days 1-2)
    brussels_days = 2
    brussels_start = 1
    brussels_end = 2

    # Variables for Barcelona stays
    barcelona1_start = Int('barcelona1_start')
    barcelona1_end = Int('barcelona1_end')
    barcelona2_start = Int('barcelona2_start')
    barcelona2_end = Int('barcelona2_end')

    # Variables for Split stay
    split_start = Int('split_start')
    split_end = Int('split_end')

    # Constraints
    s.add(barcelona1_start == 3)  # Must fly to Barcelona after Brussels
    s.add(barcelona1_end >= barcelona1_start)
    s.add(split_start == barcelona1_end)  # Fly to Split after first Barcelona stay
    s.add(split_end == split_start + 4)  # Split stay is 5 days (inclusive)
    s.add(barcelona2_start == split_end)  # Fly back to Barcelona after Split
    s.add(barcelona2_end == 12)  # Trip ends on day 12

    # Barcelona days calculation
    barcelona_days = (barcelona1_end - barcelona1_start + 1) + (barcelona2_end - barcelona2_start + 1)
    s.add(barcelona_days == 7)

    # Solve
    if s.check() == sat:
        m = s.model()
        b1_start = m.evaluate(barcelona1_start).as_long()
        b1_end = m.evaluate(barcelona1_end).as_long()
        s_start = m.evaluate(split_start).as_long()
        s_end = m.evaluate(split_end).as_long()
        b2_start = m.evaluate(barcelona2_start).as_long()
        b2_end = m.evaluate(barcelona2_end).as_long()

        itinerary = [
            {"day_range": "Day 1-2", "place": "Brussels"},
            {"day_range": f"Day {b1_start}", "place": "Barcelona"},
            {"day_range": f"Day {b1_start}-{b1_end}", "place": "Barcelona"},
            {"day_range": f"Day {s_start}", "place": "Barcelona"},
            {"day_range": f"Day {s_start}", "place": "Split"},
            {"day_range": f"Day {s_start}-{s_end}", "place": "Split"},
            {"day_range": f"Day {b2_start}", "place": "Split"},
            {"day_range": f"Day {b2_start}", "place": "Barcelona"},
            {"day_range": f"Day {b2_start}-{b2_end}", "place": "Barcelona"}
        ]

        # Simplify by merging consecutive same-city entries
        simplified = []
        prev = None
        for entry in itinerary:
            if prev and entry['place'] == prev['place']:
                # Merge ranges
                start = prev['day_range'].split('-')[0].split()[1]
                end = entry['day_range'].split('-')[-1]
                prev['day_range'] = f"Day {start}-{end}"
            else:
                simplified.append(entry)
                prev = entry

        return {"itinerary": simplified}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(result)