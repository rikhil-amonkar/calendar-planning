from z3 import *
import datetime

def solve_scheduling_problem():
    # Initialize solver
    solver = Solver()

    # Define variables (in minutes from 9:00 AM)
    richard_start = Int('richard_start')
    richard_end = Int('richard_end')
    charles_start = Int('charles_start')
    charles_end = Int('charles_end')

    # Availability windows (minutes from 9:00 AM)
    richard_min = -15  # 8:45 AM (525 - 540)
    richard_max = 240  # 1:00 PM (780 - 540)
    charles_min = 45   # 9:45 AM (585 - 540)
    charles_max = 240  # 1:00 PM (780 - 540)

    # Meeting duration constraints
    solver.add(richard_end - richard_start >= 120)
    solver.add(charles_end - charles_start >= 120)

    # Availability window constraints
    solver.add(richard_start >= richard_min)
    solver.add(richard_end <= richard_max)
    solver.add(charles_start >= charles_min)
    solver.add(charles_end <= charles_max)

    # Travel times (minutes)
    bayview_to_union = 17
    union_to_presidio = 24

    # Meeting sequence: Bayview -> Union Square -> Presidio
    solver.add(richard_start == bayview_to_union)  # Arrive at Union Square at 9:17 AM
    solver.add(charles_start == richard_end + union_to_presidio)

    # Verify Charles meeting starts within his availability
    solver.add(charles_start >= charles_min)
    solver.add(charles_end <= charles_max)

    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        
        # Get meeting times
        rs = model.evaluate(richard_start).as_long()
        re = model.evaluate(richard_end).as_long()
        cs = model.evaluate(charles_start).as_long()
        ce = model.evaluate(charles_end).as_long()

        # Convert to HH:MM format
        def to_time(minutes):
            time = datetime.datetime(2000, 1, 1, 9, 0) + datetime.timedelta(minutes=minutes)
            return time.strftime("%H:%M")

        itinerary = [
            {"action": "meet", "person": "Richard", 
             "start_time": to_time(rs), "end_time": to_time(re)},
            {"action": "meet", "person": "Charles", 
             "start_time": to_time(cs), "end_time": to_time(ce)}
        ]
        
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute and print result
print(solve_scheduling_problem())