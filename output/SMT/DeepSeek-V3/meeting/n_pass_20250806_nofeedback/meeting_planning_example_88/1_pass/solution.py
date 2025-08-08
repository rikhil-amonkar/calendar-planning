from z3 import *
import datetime

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define variables
    meet_start = Int('meet_start')  # Minutes since 9:00 AM
    meet_duration = Int('meet_duration')  # Minutes

    # Constraints
    # Joshua's availability: 8:45 PM to 9:45 PM (1170 to 1230 minutes since 9:00 AM)
    s.add(meet_start >= 705)  # 8:45 PM is 11 hours and 45 minutes after 9:00 AM (11*60 + 45 = 705)
    s.add(meet_start + meet_duration <= 765)  # 9:45 PM is 12 hours and 45 minutes after 9:00 AM (12*60 + 45 = 765)
    s.add(meet_duration >= 15)  # Minimum meeting duration

    # Travel constraints
    # To meet Joshua, you need to leave Sunset District at (meet_start - 11) minutes
    s.add(meet_start - 11 >= 0)  # Can't leave before 9:00 AM (0 minutes)

    # Optimize for maximum meeting duration
    maximize = meet_duration
    s.push()
    s.add(maximize == 60)  # Try to meet for the full hour
    if s.check() == sat:
        m = s.model()
        meet_start_val = m[meet_start].as_long()
        meet_duration_val = m[meet_duration].as_long()
    else:
        s.pop()
        s.add(maximize >= 15)  # At least 15 minutes
        if s.check() == sat:
            m = s.model()
            meet_start_val = m[meet_start].as_long()
            meet_duration_val = m[meet_duration].as_long()
        else:
            return {"itinerary": []}

    # Convert minutes to time strings
    base_time = datetime.datetime(2023, 1, 1, 9, 0)  # 9:00 AM
    start_time = base_time + datetime.timedelta(minutes=meet_start_val)
    end_time = start_time + datetime.timedelta(minutes=meet_duration_val)

    itinerary = {
        "itinerary": [
            {
                "action": "meet",
                "person": "Joshua",
                "start_time": start_time.strftime("%H:%M"),
                "end_time": end_time.strftime("%H:%M")
            }
        ]
    }

    return itinerary

# Print the solution
print(solve_scheduling())