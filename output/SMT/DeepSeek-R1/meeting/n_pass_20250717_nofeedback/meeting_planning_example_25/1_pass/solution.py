import json
from z3 import *

def main():
    # Convert all times to minutes since midnight
    start_ggp = 9 * 60  # 9:00 AM in minutes (540)
    david_start_min = 16 * 60  # 16:00 (960 minutes)
    david_end_min = 21 * 60 + 45  # 21:45 (1305 minutes)
    travel_time = 23  # minutes from Golden Gate Park to Chinatown
    min_meeting_duration = 105  # minutes

    # Initialize Z3 optimizer
    opt = Optimize()
    # Define variables: departure time from Golden Gate Park and meeting start time with David
    departure = Int('departure')
    meet_start = Int('meet_start')

    # Add constraints
    opt.add(departure >= start_ggp)  # Departure after 9:00 AM
    opt.add(meet_start >= departure + travel_time)  # Arrival before meeting start
    opt.add(meet_start >= david_start_min)  # Meeting starts at or after 4:00 PM
    opt.add(meet_start + min_meeting_duration <= david_end_min)  # Meeting ends by 9:45 PM

    # Minimize meeting start time to get the earliest possible meeting
    opt.minimize(meet_start)

    # Check for a solution
    if opt.check() == sat:
        model = opt.model()
        start_minutes = model[meet_start].as_long()
        end_minutes = start_minutes + min_meeting_duration

        # Convert minutes to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60

        start_str = f"{start_hour:02d}:{start_minute:02d}"
        end_str = f"{end_hour:02d}:{end_minute:02d}"

        # Create itinerary
        itinerary = [
            {"action": "meet", "person": "David", "start_time": start_str, "end_time": end_str}
        ]
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()