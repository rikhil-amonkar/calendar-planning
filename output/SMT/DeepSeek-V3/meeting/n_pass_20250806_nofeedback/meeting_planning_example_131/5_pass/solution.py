from z3 import *

def solve_scheduling():
    s = Solver()

    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Constants
    start_time = time_to_minutes("09:00")
    jason_start = time_to_minutes("10:00")
    jason_end = time_to_minutes("16:15")
    kenneth_start = time_to_minutes("15:30")
    kenneth_end = time_to_minutes("16:45")

    # Travel times (minutes)
    travel = {
        ('PH', 'Presidio'): 11,
        ('PH', 'Marina'): 6,
        ('Presidio', 'Marina'): 10,
        ('Marina', 'Presidio'): 10,
    }

    # Meeting variables
    j_start = Int('j_start')
    j_end = Int('j_end')
    k_start = Int('k_start')
    k_end = Int('k_end')

    # Meeting duration constraints
    s.add(j_end - j_start >= 90)  # Jason needs 90 mins
    s.add(k_end - k_start >= 45)  # Kenneth needs 45 mins

    # Availability constraints
    s.add(j_start >= jason_start, j_end <= jason_end)
    s.add(k_start >= kenneth_start, k_end <= kenneth_end)

    # Try Jason first, then Kenneth
    s.push()
    # Travel from PH to Presidio (11 min)
    s.add(j_start == start_time + travel[('PH', 'Presidio')])
    # Travel from Presidio to Marina (10 min)
    s.add(k_start == j_end + travel[('Presidio', 'Marina')])
    if s.check() == sat:
        m = s.model()
        itinerary = [
            {"action": "meet", "person": "Jason", 
             "start_time": minutes_to_time(m[j_start].as_long()),
             "end_time": minutes_to_time(m[j_end].as_long())},
            {"action": "meet", "person": "Kenneth",
             "start_time": minutes_to_time(m[k_start].as_long()),
             "end_time": minutes_to_time(m[k_end].as_long())}
        ]
        s.pop()
        return {"itinerary": itinerary}
    s.pop()

    # Try Kenneth first, then Jason
    s.push()
    # Travel from PH to Marina (6 min)
    s.add(k_start == start_time + travel[('PH', 'Marina')])
    # Travel from Marina to Presidio (10 min)
    s.add(j_start == k_end + travel[('Marina', 'Presidio')])
    if s.check() == sat:
        m = s.model()
        itinerary = [
            {"action": "meet", "person": "Kenneth",
             "start_time": minutes_to_time(m[k_start].as_long()),
             "end_time": minutes_to_time(m[k_end].as_long())},
            {"action": "meet", "person": "Jason",
             "start_time": minutes_to_time(m[j_start].as_long()),
             "end_time": minutes_to_time(m[j_end].as_long())}
        ]
        s.pop()
        return {"itinerary": itinerary}
    s.pop()

    return {"itinerary": []}

result = solve_scheduling()
print(result)