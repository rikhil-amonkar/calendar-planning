from z3 import *
import json

def solve_scheduling():
    # Create a solver instance
    s = Solver()

    # Define the variables
    # Start time of the meeting with Barbara (in minutes since 9:00 AM)
    start_barbara = Int('start_barbara')
    # Duration of the meeting with Barbara (fixed to 45 minutes)
    duration_barbara = 45

    # Constraints
    # Barbara is available from 1:15 PM to 6:15 PM (which is 255 to 555 minutes since 9:00 AM)
    s.add(start_barbara >= 255)  # 1:15 PM is 4 hours and 15 minutes after 9:00 AM
    s.add(start_barbara + duration_barbara <= 555)  # 6:15 PM is 9 hours and 15 minutes after 9:00 AM

    # Travel time from Russian Hill to Richmond District is 14 minutes
    # You can leave Russian Hill at any time, but must arrive by start_barbara
    # So the latest you can leave is start_barbara - 14
    # But since you arrive at Russian Hill at 9:00 AM (0 minutes), you can leave at any time >= 0
    s.add(start_barbara - 14 >= 0)

    # Since we want to meet as soon as possible, we minimize the start time
    s.minimize(start_barbara)

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        start = m[start_barbara].as_long()
        # Convert minutes to HH:MM format
        hours = (start // 60) + 9
        minutes = start % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        end_time = f"{(hours * 60 + minutes + duration_barbara) // 60:02d}:{(hours * 60 + minutes + duration_barbara) % 60:02d}"
        
        # Create the itinerary
        itinerary = {
            "itinerary": [
                {
                    "action": "meet",
                    "person": "Barbara",
                    "start_time": start_time,
                    "end_time": end_time
                }
            ]
        }
        print(json.dumps(itinerary, indent=2))
    else:
        print("No valid schedule found.")

solve_scheduling()