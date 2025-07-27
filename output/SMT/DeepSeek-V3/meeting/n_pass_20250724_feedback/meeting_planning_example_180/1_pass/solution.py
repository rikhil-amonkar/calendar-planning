from z3 import *
import datetime

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define travel times (in minutes)
    travel_times = {
        ('North Beach', 'Mission District'): 18,
        ('North Beach', 'The Castro'): 22,
        ('Mission District', 'North Beach'): 17,
        ('Mission District', 'The Castro'): 7,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Mission District'): 7
    }

    # Convert all times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = (minutes // 60) % 24
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Availability windows in minutes since 9:00 AM
    james_start = time_to_minutes("12:45") - 540  # 12:45 PM is 225 minutes after 9:00 AM
    james_end = time_to_minutes("14:00") - 540    # 2:00 PM is 300 minutes after 9:00 AM
    robert_start = time_to_minutes("12:45") - 540
    robert_end = time_to_minutes("15:15") - 540   # 3:15 PM is 375 minutes after 9:00 AM

    # Meeting durations in minutes
    james_min_duration = 75
    robert_min_duration = 30

    # Variables for meeting start times and durations
    meet_james_start = Int('meet_james_start')
    meet_james_end = Int('meet_james_end')
    meet_robert_start = Int('meet_robert_start')
    meet_robert_end = Int('meet_robert_end')

    # Constraints for James
    s.add(meet_james_start >= james_start)
    s.add(meet_james_end <= james_end)
    s.add(meet_james_end - meet_james_start >= james_min_duration)

    # Constraints for Robert
    s.add(meet_robert_start >= robert_start)
    s.add(meet_robert_end <= robert_end)
    s.add(meet_robert_end - meet_robert_start >= robert_min_duration)

    # Assume starting at North Beach at 9:00 AM (time 0 in our model)
    # Possible schedules:
    # Option 1: Meet James first, then Robert
    # Option 2: Meet Robert first, then James

    # We'll model both options and pick the feasible one.

    # Option 1: Meet James first, then Robert
    # Travel from North Beach to Mission District: 18 minutes
    # Meet James at Mission District
    # Then travel to The Castro: 7 minutes
    # Then meet Robert

    # Option 2: Meet Robert first, then James
    # Travel from North Beach to The Castro: 22 minutes
    # Meet Robert at The Castro
    # Then travel to Mission District: 7 minutes
    # Then meet James

    # We'll create two separate models and check which one is feasible.

    # Model for Option 1: James first
    s1 = Solver()
    # Start at North Beach at 0 minutes (9:00 AM)
    # Travel to Mission District: 18 minutes
    arrival_james = 18
    meet_james_start_1 = Int('meet_james_start_1')
    meet_james_end_1 = Int('meet_james_end_1')
    s1.add(meet_james_start_1 >= arrival_james)
    s1.add(meet_james_start_1 >= james_start)
    s1.add(meet_james_end_1 <= james_end)
    s1.add(meet_james_end_1 - meet_james_start_1 >= james_min_duration)

    # Travel to The Castro after meeting James: 7 minutes
    arrival_robert = meet_james_end_1 + 7
    meet_robert_start_1 = Int('meet_robert_start_1')
    meet_robert_end_1 = Int('meet_robert_end_1')
    s1.add(meet_robert_start_1 >= arrival_robert)
    s1.add(meet_robert_start_1 >= robert_start)
    s1.add(meet_robert_end_1 <= robert_end)
    s1.add(meet_robert_end_1 - meet_robert_start_1 >= robert_min_duration)

    # Check if Option 1 is feasible
    if s1.check() == sat:
        m1 = s1.model()
        js1 = m1.eval(meet_james_start_1).as_long()
        je1 = m1.eval(meet_james_end_1).as_long()
        rs1 = m1.eval(meet_robert_start_1).as_long()
        re1 = m1.eval(meet_robert_end_1).as_long()
        itinerary = [
            {"action": "meet", "person": "James", "start_time": minutes_to_time(540 + js1), "end_time": minutes_to_time(540 + je1)},
            {"action": "meet", "person": "Robert", "start_time": minutes_to_time(540 + rs1), "end_time": minutes_to_time(540 + re1)}
        ]
        return {"itinerary": itinerary}

    # Model for Option 2: Robert first
    s2 = Solver()
    # Start at North Beach at 0 minutes (9:00 AM)
    # Travel to The Castro: 22 minutes
    arrival_robert = 22
    meet_robert_start_2 = Int('meet_robert_start_2')
    meet_robert_end_2 = Int('meet_robert_end_2')
    s2.add(meet_robert_start_2 >= arrival_robert)
    s2.add(meet_robert_start_2 >= robert_start)
    s2.add(meet_robert_end_2 <= robert_end)
    s2.add(meet_robert_end_2 - meet_robert_start_2 >= robert_min_duration)

    # Travel to Mission District after meeting Robert: 7 minutes
    arrival_james = meet_robert_end_2 + 7
    meet_james_start_2 = Int('meet_james_start_2')
    meet_james_end_2 = Int('meet_james_end_2')
    s2.add(meet_james_start_2 >= arrival_james)
    s2.add(meet_james_start_2 >= james_start)
    s2.add(meet_james_end_2 <= james_end)
    s2.add(meet_james_end_2 - meet_james_start_2 >= james_min_duration)

    # Check if Option 2 is feasible
    if s2.check() == sat:
        m2 = s2.model()
        rs2 = m2.eval(meet_robert_start_2).as_long()
        re2 = m2.eval(meet_robert_end_2).as_long()
        js2 = m2.eval(meet_james_start_2).as_long()
        je2 = m2.eval(meet_james_end_2).as_long()
        itinerary = [
            {"action": "meet", "person": "Robert", "start_time": minutes_to_time(540 + rs2), "end_time": minutes_to_time(540 + re2)},
            {"action": "meet", "person": "James", "start_time": minutes_to_time(540 + js2), "end_time": minutes_to_time(540 + je2)}
        ]
        return {"itinerary": itinerary}

    # If neither option is feasible, return empty itinerary
    return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling()
print(solution)