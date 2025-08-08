from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times (in minutes since midnight)
    meet_richard_start = Int('meet_richard_start')
    meet_richard_end = Int('meet_richard_end')
    meet_charles_start = Int('meet_charles_start')
    meet_charles_end = Int('meet_charles_end')

    # Arrival at Bayview at 9:00 AM (540 minutes)
    bayview_arrival = 540

    # Richard's availability: 8:45 AM (525) to 1:00 PM (780)
    richard_start_avail = 525
    richard_end_avail = 780

    # Charles's availability: 9:45 AM (585) to 1:00 PM (780)
    charles_start_avail = 585
    charles_end_avail = 780

    # Meeting durations (minimum 120 minutes each)
    duration = 120

    # Travel times (in minutes)
    bayview_to_union = 17
    bayview_to_presidio = 31
    union_to_presidio = 24
    presidio_to_union = 22

    # Constraints for Richard's meeting
    s.add(meet_richard_start >= richard_start_avail)
    s.add(meet_richard_end <= richard_end_avail)
    s.add(meet_richard_end == meet_richard_start + duration)

    # Constraints for Charles's meeting
    s.add(meet_charles_start >= charles_start_avail)
    s.add(meet_charles_end <= charles_end_avail)
    s.add(meet_charles_end == meet_charles_start + duration)

    # Option 1: Meet Richard first, then Charles
    option1 = And(
        meet_richard_start >= bayview_arrival + bayview_to_union,
        meet_charles_start >= meet_richard_end + union_to_presidio
    )

    # Option 2: Meet Charles first, then Richard
    option2 = And(
        meet_charles_start >= bayview_arrival + bayview_to_presidio,
        meet_richard_start >= meet_charles_end + presidio_to_union
    )

    # Add either option1 or option2
    s.add(Or(option1, option2))

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        richard_start = m.evaluate(meet_richard_start).as_long()
        richard_end = m.evaluate(meet_richard_end).as_long()
        charles_start = m.evaluate(meet_charles_start).as_long()
        charles_end = m.evaluate(meet_charles_end).as_long()

        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        richard_start_time = minutes_to_time(richard_start)
        richard_end_time = minutes_to_time(richard_end)
        charles_start_time = minutes_to_time(charles_start)
        charles_end_time = minutes_to_time(charles_end)

        # Determine the order of meetings
        if richard_start < charles_start:
            itinerary = [
                {"action": "meet", "person": "Richard", "start_time": richard_start_time, "end_time": richard_end_time},
                {"action": "meet", "person": "Charles", "start_time": charles_start_time, "end_time": charles_end_time}
            ]
        else:
            itinerary = [
                {"action": "meet", "person": "Charles", "start_time": charles_start_time, "end_time": charles_end_time},
                {"action": "meet", "person": "Richard", "start_time": richard_start_time, "end_time": richard_end_time}
            ]

        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found."}

# Solve and print the result
result = solve_scheduling()
print(result)