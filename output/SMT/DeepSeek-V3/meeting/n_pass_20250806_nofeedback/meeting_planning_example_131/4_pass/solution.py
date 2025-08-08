from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Constants
    start_time = time_to_minutes("09:00")  # Arrival time at Pacific Heights
    jason_start = time_to_minutes("10:00")
    jason_end = time_to_minutes("16:15")
    kenneth_start = time_to_minutes("15:30")
    kenneth_end = time_to_minutes("16:45")

    # Travel times in minutes
    travel = {
        ('PH', 'Presidio'): 11,
        ('PH', 'Marina'): 6,
        ('Presidio', 'Marina'): 10,
        ('Marina', 'Presidio'): 10,
        ('Presidio', 'PH'): 11,
        ('Marina', 'PH'): 7
    }

    # Variables
    jason_meet_start = Int('jason_meet_start')
    jason_meet_end = Int('jason_meet_end')
    kenneth_meet_start = Int('kenneth_meet_start')
    kenneth_meet_end = Int('kenneth_meet_end')

    # Meeting duration constraints
    s.add(jason_meet_end - jason_meet_start >= 90)
    s.add(kenneth_meet_end - kenneth_meet_start >= 45)

    # Availability constraints
    s.add(jason_meet_start >= jason_start)
    s.add(jason_meet_end <= jason_end)
    s.add(kenneth_meet_start >= kenneth_start)
    s.add(kenneth_meet_end <= kenneth_end)

    # Try meeting Jason first
    s.push()
    # Travel from PH to Presidio (11 min) after 9:00
    s.add(jason_meet_start == start_time + travel[('PH', 'Presidio')])
    # Then travel to Marina (10 min) after meeting Jason
    s.add(kenneth_meet_start == jason_meet_end + travel[('Presidio', 'Marina')])
    # Check if Kenneth's meeting fits
    s.add(kenneth_meet_end <= kenneth_end)

    if s.check() == sat:
        model = s.model()
        itinerary = [
            {
                "action": "meet",
                "person": "Jason",
                "start_time": minutes_to_time(model.eval(jason_meet_start).as_long()),
                "end_time": minutes_to_time(model.eval(jason_meet_end).as_long())
            },
            {
                "action": "meet",
                "person": "Kenneth",
                "start_time": minutes_to_time(model.eval(kenneth_meet_start).as_long()),
                "end_time": minutes_to_time(model.eval(kenneth_meet_end).as_long())
            }
        ]
        s.pop()
        return {"itinerary": itinerary}
    s.pop()

    # Try meeting Kenneth first
    s.push()
    # Travel from PH to Marina (6 min) after 9:00
    s.add(kenneth_meet_start == start_time + travel[('PH', 'Marina')])
    # Then travel to Presidio (10 min) after meeting Kenneth
    s.add(jason_meet_start == kenneth_meet_end + travel[('Marina', 'Presidio')])
    # Check if Jason's meeting fits
    s.add(jason_meet_end <= jason_end)

    if s.check() == sat:
        model = s.model()
        itinerary = [
            {
                "action": "meet",
                "person": "Kenneth",
                "start_time": minutes_to_time(model.eval(kenneth_meet_start).as_long()),
                "end_time": minutes_to_time(model.eval(kenneth_meet_end).as_long())
            },
            {
                "action": "meet",
                "person": "Jason",
                "start_time": minutes_to_time(model.eval(jason_meet_start).as_long()),
                "end_time": minutes_to_time(model.eval(jason_meet_end).as_long())
            }
        ]
        s.pop()
        return {"itinerary": itinerary}
    s.pop()

    # No feasible schedule found
    return {"itinerary": []}

# Solve and print the result
result = solve_scheduling()
print(result)