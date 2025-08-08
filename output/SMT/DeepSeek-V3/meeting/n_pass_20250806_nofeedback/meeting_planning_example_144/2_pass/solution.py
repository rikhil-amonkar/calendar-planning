from z3 import *

def solve_scheduling_problem():
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

    # Time constraints in minutes since 9:00 AM (540)
    laura_start = time_to_minutes("12:15") - 540
    laura_end = time_to_minutes("19:45") - 540
    anthony_start = time_to_minutes("12:30") - 540
    anthony_end = time_to_minutes("14:45") - 540

    # Meeting durations in minutes
    laura_duration = 75
    anthony_duration = 30

    # Travel times between locations (in minutes)
    travel = {
        ('The Castro', 'Mission District'): 7,
        ('The Castro', 'Financial District'): 20,
        ('Mission District', 'The Castro'): 7,
        ('Mission District', 'Financial District'): 17,
        ('Financial District', 'The Castro'): 23,
        ('Financial District', 'Mission District'): 17,
    }

    # Variables for meeting start times (in minutes since 9:00 AM)
    meet_laura_start = Int('meet_laura_start')
    meet_laura_end = Int('meet_laura_end')
    meet_anthony_start = Int('meet_anthony_start')
    meet_anthony_end = Int('meet_anthony_end')

    # Constraints for Laura's meeting
    s.add(meet_laura_start >= laura_start)
    s.add(meet_laura_end <= laura_end)
    s.add(meet_laura_end == meet_laura_start + laura_duration)

    # Constraints for Anthony's meeting
    s.add(meet_anthony_start >= anthony_start)
    s.add(meet_anthony_end <= anthony_end)
    s.add(meet_anthony_end == meet_anthony_start + anthony_duration)

    # Possible orders of meetings: Laura first or Anthony first
    # Option 1: Meet Laura first, then Anthony
    option1 = And(
        meet_laura_start >= travel['The Castro', 'Mission District'],
        meet_laura_end + travel['Mission District', 'Financial District'] <= meet_anthony_start
    )

    # Option 2: Meet Anthony first, then Laura
    option2 = And(
        meet_anthony_start >= travel['The Castro', 'Financial District'],
        meet_anthony_end + travel['Financial District', 'Mission District'] <= meet_laura_start
    )

    # Add disjunction of the two options
    s.add(Or(option1, option2))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        # Extract meeting times
        laura_start_time = m.evaluate(meet_laura_start).as_long()
        laura_end_time = m.evaluate(meet_laura_end).as_long()
        anthony_start_time = m.evaluate(meet_anthony_start).as_long()
        anthony_end_time = m.evaluate(meet_anthony_end).as_long()

        # Convert back to absolute times (from 9:00 AM)
        absolute_start_laura = 540 + laura_start_time
        absolute_end_laura = 540 + laura_end_time
        absolute_start_anthony = 540 + anthony_start_time
        absolute_end_anthony = 540 + anthony_end_time

        # Determine the order of meetings
        if laura_start_time + laura_duration + travel['Mission District', 'Financial District'] <= anthony_start_time:
            # Laura first
            itinerary = [
                {
                    "action": "meet",
                    "person": "Laura",
                    "start_time": minutes_to_time(absolute_start_laura),
                    "end_time": minutes_to_time(absolute_end_laura)
                },
                {
                    "action": "meet",
                    "person": "Anthony",
                    "start_time": minutes_to_time(absolute_start_anthony),
                    "end_time": minutes_to_time(absolute_end_anthony)
                }
            ]
        else:
            # Anthony first
            itinerary = [
                {
                    "action": "meet",
                    "person": "Anthony",
                    "start_time": minutes_to_time(absolute_start_anthony),
                    "end_time": minutes_to_time(absolute_end_anthony)
                },
                {
                    "action": "meet",
                    "person": "Laura",
                    "start_time": minutes_to_time(absolute_start_laura),
                    "end_time": minutes_to_time(absolute_end_laura)
                }
            ]

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(solution)