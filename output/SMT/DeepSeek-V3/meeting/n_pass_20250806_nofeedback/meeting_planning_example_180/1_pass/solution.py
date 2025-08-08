from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define variables for meeting start and end times
    # Meeting James at Mission District
    meet_james_start = Int('meet_james_start')  # in minutes since 9:00 AM
    meet_james_end = Int('meet_james_end')

    # Meeting Robert at The Castro
    meet_robert_start = Int('meet_robert_start')
    meet_robert_end = Int('meet_robert_end')

    # Convert friend availability windows to minutes since 9:00 AM
    # James is available from 12:45 PM to 2:00 PM (225 to 300 minutes since 9:00 AM)
    james_window_start = 225  # 12:45 PM is 3 hours 45 minutes after 9:00 AM
    james_window_end = 300    # 2:00 PM is 5 hours after 9:00 AM

    # Robert is available from 12:45 PM to 3:15 PM (225 to 375 minutes)
    robert_window_start = 225
    robert_window_end = 375

    # Constraints for James
    s.add(meet_james_start >= james_window_start)
    s.add(meet_james_end <= james_window_end)
    s.add(meet_james_end - meet_james_start >= 75)  # at least 75 minutes

    # Constraints for Robert
    s.add(meet_robert_start >= robert_window_start)
    s.add(meet_robert_end <= robert_window_end)
    s.add(meet_robert_end - meet_robert_start >= 30)  # at least 30 minutes

    # Travel times (in minutes)
    # From North Beach to Mission District: 18
    # From Mission District to The Castro: 7
    # From The Castro to Mission District: 7
    # etc.

    # Assume we start at North Beach at time 0 (9:00 AM)
    # We need to decide the order of meetings: James first or Robert first.

    # We'll model both possible orders and let Z3 choose the feasible one.

    # Order 1: Meet James first, then Robert
    travel_james = 18  # North Beach to Mission District
    travel_robert = 7  # Mission District to The Castro

    # Constraints for Order 1
    order1 = And(
        meet_james_start >= travel_james,  # time to travel to James
        meet_robert_start >= meet_james_end + 7  # time to travel to Robert after meeting James
    )

    # Order 2: Meet Robert first, then James
    travel_robert_first = 22  # North Beach to The Castro
    travel_james_after = 7    # The Castro to Mission District

    order2 = And(
        meet_robert_start >= travel_robert_first,
        meet_james_start >= meet_robert_end + 7
    )

    # Add either order1 or order2 to the solver
    s.add(Or(order1, order2))

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        # Get the meeting times
        james_start = m.evaluate(meet_james_start).as_long()
        james_end = m.evaluate(meet_james_end).as_long()
        robert_start = m.evaluate(meet_robert_start).as_long()
        robert_end = m.evaluate(meet_robert_end).as_long()

        # Convert minutes since 9:00 AM to HH:MM format
        def to_time_str(minutes):
            hours = 9 + (minutes // 60)
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        james_start_str = to_time_str(james_start)
        james_end_str = to_time_str(james_end)
        robert_start_str = to_time_str(robert_start)
        robert_end_str = to_time_str(robert_end)

        # Determine the order of meetings
        if james_start < robert_start:
            itinerary = [
                {"action": "meet", "person": "James", "start_time": james_start_str, "end_time": james_end_str},
                {"action": "meet", "person": "Robert", "start_time": robert_start_str, "end_time": robert_end_str}
            ]
        else:
            itinerary = [
                {"action": "meet", "person": "Robert", "start_time": robert_start_str, "end_time": robert_end_str},
                {"action": "meet", "person": "James", "start_time": james_start_str, "end_time": james_end_str}
            ]

        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found."}

# Solve and print the result
result = solve_scheduling()
print(result)