from z3 import *
import datetime

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times
    # Richard is at Union Square from 8:45 to 13:00
    # Charles is at Presidio from 9:45 to 13:00
    # All times are in minutes since 9:00 AM (540 minutes since midnight)

    # Convert all times to minutes since midnight for easier arithmetic
    # Arrival at Bayview: 9:00 AM (540 minutes)
    bayview_arrival = 540

    # Richard's availability: 8:45 AM (525) to 13:00 (780)
    richard_start_avail = 525
    richard_end_avail = 780

    # Charles's availability: 9:45 AM (585) to 13:00 (780)
    charles_start_avail = 585
    charles_end_avail = 780

    # Meeting durations (minimum 120 minutes each)
    duration = 120

    # Travel times (in minutes)
    bayview_to_union = 17
    bayview_to_presidio = 31
    union_to_bayview = 15
    union_to_presidio = 24
    presidio_to_bayview = 31
    presidio_to_union = 22

    # Decision variables: start times of meetings
    # We can choose to meet Richard first or Charles first, or only one of them.
    # But given the constraints, we likely need to meet both.

    # Let's define start times for each meeting.
    meet_richard_start = Int('meet_richard_start')
    meet_richard_end = Int('meet_richard_end')
    meet_charles_start = Int('meet_charles_start')
    meet_charles_end = Int('meet_charles_end')

    # Constraints for Richard's meeting
    s.add(meet_richard_start >= richard_start_avail)
    s.add(meet_richard_end <= richard_end_avail)
    s.add(meet_richard_end == meet_richard_start + duration)

    # Constraints for Charles's meeting
    s.add(meet_charles_start >= charles_start_avail)
    s.add(meet_charles_end <= charles_end_avail)
    s.add(meet_charles_end == meet_charles_start + duration)

    # Now, the travel constraints.
    # We start at Bayview at 540.
    # Possible schedules:
    # Option 1: Bayview -> Union (Richard) -> Presidio (Charles)
    # Option 2: Bayview -> Presidio (Charles) -> Union (Richard)
    # We'll model both options and let Z3 choose the feasible one.

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