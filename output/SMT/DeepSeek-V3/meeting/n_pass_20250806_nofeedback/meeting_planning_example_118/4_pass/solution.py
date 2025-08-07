from z3 import *

def solve_scheduling():
    s = Solver()

    # Time variables in minutes since midnight
    bayview_arrival = 540  # 9:00 AM
    richard_start_avail = 525  # 8:45 AM
    richard_end_avail = 780  # 1:00 PM
    charles_start_avail = 585  # 9:45 AM
    charles_end_avail = 780  # 1:00 PM

    # Travel times
    bayview_to_union = 17
    bayview_to_presidio = 31
    union_to_presidio = 24
    presidio_to_union = 22

    # Meeting duration variables
    meet_richard = Int('meet_richard')
    meet_charles = Int('meet_charles')
    min_duration = 120

    # We'll try to meet both, but may need to reduce time with one
    s.add(meet_richard >= min_duration)
    s.add(meet_charles >= min_duration)

    # Meeting start times
    richard_start = Int('richard_start')
    richard_end = Int('richard_end')
    charles_start = Int('charles_start')
    charles_end = Int('charles_end')

    # Basic meeting constraints
    s.add(richard_start >= richard_start_avail)
    s.add(richard_end <= richard_end_avail)
    s.add(richard_end == richard_start + meet_richard)
    
    s.add(charles_start >= charles_start_avail)
    s.add(charles_end <= charles_end_avail)
    s.add(charles_end == charles_start + meet_charles)

    # Try meeting Richard first
    option1 = And(
        richard_start >= bayview_arrival + bayview_to_union,
        charles_start >= richard_end + union_to_presidio
    )

    # Try meeting Charles first
    option2 = And(
        charles_start >= bayview_arrival + bayview_to_presidio,
        richard_start >= charles_end + presidio_to_union
    )

    s.add(Or(option1, option2))

    # If we can't meet both for 120 minutes, relax one duration
    if s.check() != sat:
        s.reset()
        s.add(Or(
            And(meet_richard >= min_duration, meet_charles >= 60),  # At least 1 hour with Charles
            And(meet_charles >= min_duration, meet_richard >= 60)   # At least 1 hour with Richard
        ))
        # Re-add all other constraints
        s.add(richard_start >= richard_start_avail)
        s.add(richard_end <= richard_end_avail)
        s.add(richard_end == richard_start + meet_richard)
        s.add(charles_start >= charles_start_avail)
        s.add(charles_end <= charles_end_avail)
        s.add(charles_end == charles_start + meet_charles)
        s.add(Or(option1, option2))

    if s.check() == sat:
        m = s.model()
        richard_start = m.evaluate(richard_start).as_long()
        richard_end = m.evaluate(richard_end).as_long()
        charles_start = m.evaluate(charles_start).as_long()
        charles_end = m.evaluate(charles_end).as_long()
        meet_richard = m.evaluate(meet_richard).as_long()
        meet_charles = m.evaluate(meet_charles).as_long()

        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        itinerary = []
        if richard_start < charles_start:
            itinerary.extend([
                {"action": "meet", "person": "Richard", "start_time": minutes_to_time(richard_start), 
                 "end_time": minutes_to_time(richard_end)},
                {"action": "meet", "person": "Charles", "start_time": minutes_to_time(charles_start), 
                 "end_time": minutes_to_time(charles_end)}
            ])
        else:
            itinerary.extend([
                {"action": "meet", "person": "Charles", "start_time": minutes_to_time(charles_start), 
                 "end_time": minutes_to_time(charles_end)},
                {"action": "meet", "person": "Richard", "start_time": minutes_to_time(richard_start), 
                 "end_time": minutes_to_time(richard_end)}
            ])

        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found even with reduced meeting times."}

result = solve_scheduling()
print(result)