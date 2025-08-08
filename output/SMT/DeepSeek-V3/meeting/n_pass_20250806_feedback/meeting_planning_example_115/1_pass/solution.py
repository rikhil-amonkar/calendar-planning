from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define variables for meeting start and end times
    # Carol's meeting at Marina District
    carol_start = Int('carol_start')  # in minutes from 9:00 AM
    carol_end = Int('carol_end')

    # Jessica's meeting at Pacific Heights
    jessica_start = Int('jessica_start')  # in minutes from 9:00 AM
    jessica_end = Int('jessica_end')

    # Convert time constraints to minutes from 9:00 AM
    # Carol is available from 11:30 AM to 3:00 PM (150 to 360 minutes from 9:00 AM)
    carol_available_start = 150  # 11:30 AM is 2.5 hours after 9:00 AM
    carol_available_end = 360    # 3:00 PM is 6 hours after 9:00 AM

    # Jessica is available from 3:30 PM to 4:45 PM (390 to 465 minutes from 9:00 AM)
    jessica_available_start = 390  # 3:30 PM is 6.5 hours after 9:00 AM
    jessica_available_end = 465    # 4:45 PM is 7.75 hours after 9:00 AM

    # Travel times in minutes
    richmond_to_marina = 9
    richmond_to_pacific = 10
    marina_to_pacific = 7
    pacific_to_marina = 6
    marina_to_richmond = 11
    pacific_to_richmond = 12

    # Constraints for Carol's meeting
    s.add(carol_start >= carol_available_start)
    s.add(carol_end <= carol_available_end)
    s.add(carol_end - carol_start >= 60)  # at least 60 minutes

    # Constraints for Jessica's meeting
    s.add(jessica_start >= jessica_available_start)
    s.add(jessica_end <= jessica_available_end)
    s.add(jessica_end - jessica_start >= 45)  # at least 45 minutes

    # Starting at Richmond District at 0 minutes (9:00 AM)
    # Possible sequences:
    # 1. Go to Marina to meet Carol, then to Pacific to meet Jessica
    # 2. Go to Pacific to meet Jessica, but this is not possible because Jessica's time is after Carol's
    # So only sequence 1 is feasible.

    # Sequence: Richmond -> Marina -> Pacific
    s.add(carol_start >= richmond_to_marina)  # time to reach Marina
    s.add(jessica_start >= carol_end + marina_to_pacific)  # time to reach Pacific from Marina

    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        # Extract the meeting times
        carol_s = m.eval(carol_start).as_long()
        carol_e = m.eval(carol_end).as_long()
        jessica_s = m.eval(jessica_start).as_long()
        jessica_e = m.eval(jessica_end).as_long()

        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            hours = 9 + (minutes // 60)
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        carol_start_time = minutes_to_time(carol_s)
        carol_end_time = minutes_to_time(carol_e)
        jessica_start_time = minutes_to_time(jessica_s)
        jessica_end_time = minutes_to_time(jessica_e)

        itinerary = [
            {"action": "meet", "person": "Carol", "start_time": carol_start_time, "end_time": carol_end_time},
            {"action": "meet", "person": "Jessica", "start_time": jessica_start_time, "end_time": jessica_end_time}
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the solver and print the result
result = solve_scheduling()
print(result)