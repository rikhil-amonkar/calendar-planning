from z3 import *

def solve_itinerary():
    s = Solver()

    # Variables for start and end days in each city
    m_start = Int('m_start')
    m_end = Int('m_end')
    d_start = Int('d_start')
    d_end = Int('d_end')
    t_start = Int('t_start')
    t_end = Int('t_end')

    # Day ranges
    s.add(m_start >= 1, m_end <= 7)
    s.add(d_start >= 1, d_end <= 7)
    s.add(t_start >= 1, t_end <= 7)

    # Days in each city
    s.add(m_end - m_start + 1 == 4)  # Madrid: 4 days
    s.add(d_end - d_start + 1 == 3)   # Dublin: 3 days
    s.add(t_end - t_start + 1 == 2)   # Tallinn: 2 days

    # Workshop in Tallinn between day 6 and day 7
    s.add(t_start <= 6, t_end >= 6)

    # Flight constraints: Madrid <-> Dublin <-> Tallinn
    # Possible orders: Madrid -> Dublin -> Tallinn or Tallinn -> Dublin -> Madrid
    order1 = And(m_end == d_start, d_end == t_start)
    order2 = And(t_end == d_start, d_end == m_start)
    s.add(Or(order1, order2))

    if s.check() == sat:
        model = s.model()
        m_start_val = model[m_start].as_long()
        m_end_val = model[m_end].as_long()
        d_start_val = model[d_start].as_long()
        d_end_val = model[d_end].as_long()
        t_start_val = model[t_start].as_long()
        t_end_val = model[t_end].as_long()

        itinerary = []

        # Madrid stay
        if m_start_val < m_end_val:
            itinerary.append({"day_range": f"Day {m_start_val}-{m_end_val}", "place": "Madrid"})
        else:
            itinerary.append({"day_range": f"Day {m_start_val}", "place": "Madrid"})

        # Flight to Dublin
        itinerary.append({"day_range": f"Day {m_end_val}", "place": "Madrid"})
        itinerary.append({"day_range": f"Day {d_start_val}", "place": "Dublin"})

        # Dublin stay
        if d_start_val < d_end_val:
            itinerary.append({"day_range": f"Day {d_start_val}-{d_end_val}", "place": "Dublin"})
        else:
            itinerary.append({"day_range": f"Day {d_start_val}", "place": "Dublin"})

        # Flight to Tallinn
        itinerary.append({"day_range": f"Day {d_end_val}", "place": "Dublin"})
        itinerary.append({"day_range": f"Day {t_start_val}", "place": "Tallinn"})

        # Tallinn stay
        if t_start_val < t_end_val:
            itinerary.append({"day_range": f"Day {t_start_val}-{t_end_val}", "place": "Tallinn"})
        else:
            itinerary.append({"day_range": f"Day {t_start_val}", "place": "Tallinn"})

        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))