from z3 import *
import datetime

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Define variables for meeting start and end times in minutes since 9:00 AM
    # James is at Mission District from 12:45 (765 minutes) to 14:00 (840 minutes)
    # Robert is at The Castro from 12:45 (765 minutes) to 15:15 (915 minutes)
    james_start = time_to_minutes("12:45")
    james_end = time_to_minutes("14:00")
    robert_start = time_to_minutes("12:45")
    robert_end = time_to_minutes("15:15")

    # Variables for meeting James
    meet_james_start = Int('meet_james_start')
    meet_james_end = Int('meet_james_end')
    meet_james_duration = 75  # minutes

    # Variables for meeting Robert
    meet_robert_start = Int('meet_robert_start')
    meet_robert_end = Int('meet_robert_end')
    meet_robert_duration = 30  # minutes

    # Constraints for meeting James
    s.add(meet_james_start >= james_start)
    s.add(meet_james_end <= james_end)
    s.add(meet_james_end == meet_james_start + meet_james_duration)

    # Constraints for meeting Robert
    s.add(meet_robert_start >= robert_start)
    s.add(meet_robert_end <= robert_end)
    s.add(meet_robert_end == meet_robert_start + meet_robert_duration)

    # Travel times
    # From North Beach to Mission District: 18 minutes
    # From Mission District to The Castro: 7 minutes
    # From The Castro to Mission District: 7 minutes
    # From Mission District to North Beach: 17 minutes
    # From The Castro to North Beach: 20 minutes
    # From North Beach to The Castro: 22 minutes

    # We need to decide the order of meetings: James first or Robert first.

    # Scenario 1: Meet James first, then Robert
    scenario1 = Solver()
    scenario1.add(meet_james_start >= 540 + 18)  # Start at North Beach at 9:00 (540), travel to Mission District takes 18 minutes
    scenario1.add(meet_robert_start >= meet_james_end + 7)  # Travel from Mission District to The Castro takes 7 minutes
    scenario1.add(meet_james_start >= james_start)
    scenario1.add(meet_james_end <= james_end)
    scenario1.add(meet_james_end == meet_james_start + meet_james_duration)
    scenario1.add(meet_robert_start >= robert_start)
    scenario1.add(meet_robert_end <= robert_end)
    scenario1.add(meet_robert_end == meet_robert_start + meet_robert_duration)

    # Scenario 2: Meet Robert first, then James
    scenario2 = Solver()
    scenario2.add(meet_robert_start >= 540 + 22)  # Travel from North Beach to The Castro takes 22 minutes
    scenario2.add(meet_james_start >= meet_robert_end + 7)  # Travel from The Castro to Mission District takes 7 minutes
    scenario2.add(meet_james_start >= james_start)
    scenario2.add(meet_james_end <= james_end)
    scenario2.add(meet_james_end == meet_james_start + meet_james_duration)
    scenario2.add(meet_robert_start >= robert_start)
    scenario2.add(meet_robert_end <= robert_end)
    scenario2.add(meet_robert_end == meet_robert_start + meet_robert_duration)

    itinerary = []

    # Check which scenario is feasible
    if scenario1.check() == sat:
        m = scenario1.model()
        j_s = m.eval(meet_james_start).as_long()
        j_e = m.eval(meet_james_end).as_long()
        r_s = m.eval(meet_robert_start).as_long()
        r_e = m.eval(meet_robert_end).as_long()

        itinerary = [
            {"action": "meet", "person": "James", "start_time": minutes_to_time(j_s), "end_time": minutes_to_time(j_e)},
            {"action": "meet", "person": "Robert", "start_time": minutes_to_time(r_s), "end_time": minutes_to_time(r_e)}
        ]
    elif scenario2.check() == sat:
        m = scenario2.model()
        r_s = m.eval(meet_robert_start).as_long()
        r_e = m.eval(meet_robert_end).as_long()
        j_s = m.eval(meet_james_start).as_long()
        j_e = m.eval(meet_james_end).as_long()

        itinerary = [
            {"action": "meet", "person": "Robert", "start_time": minutes_to_time(r_s), "end_time": minutes_to_time(r_e)},
            {"action": "meet", "person": "James", "start_time": minutes_to_time(j_s), "end_time": minutes_to_time(j_e)}
        ]
    else:
        return {"itinerary": []}

    return {"itinerary": itinerary}

result = solve_scheduling()
print(result)