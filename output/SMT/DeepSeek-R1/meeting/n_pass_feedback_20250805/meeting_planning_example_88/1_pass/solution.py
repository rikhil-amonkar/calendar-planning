from z3 import *
import json

def main():
    # Convert times to minutes since midnight
    start_time = 9 * 60  # 9:00 AM (540 minutes)
    joshua_start = 20 * 60 + 45  # 8:45 PM (1245 minutes)
    joshua_end = 21 * 60 + 45    # 9:45 PM (1305 minutes)

    s = Solver()

    # Departure time from Sunset District (minutes)
    depart_sunset = Int('depart_sunset')
    # Meeting start time with Joshua (minutes)
    meet_start = Int('meet_start')

    # Constraints
    s.add(depart_sunset >= start_time)  # Cannot leave before 9:00 AM
    arrive_ggp = depart_sunset + 11     # Arrival at Golden Gate Park
    s.add(arrive_ggp <= meet_start)     # Must arrive before meeting starts
    s.add(meet_start >= joshua_start)   # Meeting must start during Joshua's availability
    meet_end = meet_start + 15          # Meeting duration is 15 minutes
    s.add(meet_end <= joshua_end)       # Meeting must end by 9:45 PM

    if s.check() == sat:
        m = s.model()
        meet_start_min = m[meet_start].as_long()
        meet_end_min = meet_start_min + 15

        # Format times to HH:MM
        def format_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        meet_start_str = format_time(meet_start_min)
        meet_end_str = format_time(meet_end_min)

        itinerary = [{
            "action": "meet",
            "person": "Joshua",
            "start_time": meet_start_str,
            "end_time": meet_end_str
        }]

        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()