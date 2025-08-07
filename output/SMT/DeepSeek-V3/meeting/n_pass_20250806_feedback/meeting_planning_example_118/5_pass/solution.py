from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting times (in minutes since 9:00 AM)
    richard_start = Int('richard_start')
    richard_end = Int('richard_end')
    charles_start = Int('charles_start')
    charles_end = Int('charles_end')

    # Friend availability windows (minutes since 9:00 AM)
    richard_available_start = -15  # 8:45 AM
    richard_available_end = 240    # 1:00 PM
    charles_available_start = 45   # 9:45 AM
    charles_available_end = 240    # 1:00 PM

    # Travel times (minutes)
    bayview_to_union_square = 17
    bayview_to_presidio = 31
    union_square_to_presidio = 24
    presidio_to_union_square = 22

    # Meeting duration constraints
    s.add(richard_end - richard_start >= 120)
    s.add(charles_end - charles_start >= 120)

    # Availability constraints
    s.add(richard_start >= richard_available_start)
    s.add(richard_end <= richard_available_end)
    s.add(charles_start >= charles_available_start)
    s.add(charles_end <= charles_available_end)

    # Define both possible meeting sequences
    # Option 1: Richard first, then Charles
    option1 = And(
        richard_start >= bayview_to_union_square,  # Travel to Richard
        charles_start >= richard_end + union_square_to_presidio,  # Travel to Charles
        charles_end <= charles_available_end  # Ensure Charles meeting fits
    )

    # Option 2: Charles first, then Richard
    option2 = And(
        charles_start >= bayview_to_presidio,  # Travel to Charles
        richard_start >= charles_end + presidio_to_union_square,  # Travel to Richard
        richard_end <= richard_available_end  # Ensure Richard meeting fits
    )

    s.add(Or(option1, option2))

    # Check for solution
    if s.check() == sat:
        m = s.model()
        # Convert times to HH:MM format
        def to_time(minutes):
            h = (540 + minutes) // 60  # 9:00 AM = 540 minutes
            m = (540 + minutes) % 60
            return f"{h:02d}:{m:02d}"

        rs = m.evaluate(richard_start).as_long()
        re = m.evaluate(richard_end).as_long()
        cs = m.evaluate(charles_start).as_long()
        ce = m.evaluate(charles_end).as_long()

        # Determine meeting order
        if rs < cs:
            itinerary = [
                {"action": "meet", "person": "Richard", "start_time": to_time(rs), "end_time": to_time(re)},
                {"action": "meet", "person": "Charles", "start_time": to_time(cs), "end_time": to_time(ce)}
            ]
        else:
            itinerary = [
                {"action": "meet", "person": "Charles", "start_time": to_time(cs), "end_time": to_time(ce)},
                {"action": "meet", "person": "Richard", "start_time": to_time(rs), "end_time": to_time(re)}
            ]

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print result
result = solve_scheduling()
print(result)