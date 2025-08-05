from z3 import *
import json

def main():
    # Convert time constraints to minutes since 9:00 AM
    timothy_start = (20 - 9) * 60 + 45  # 20:45 -> 705 minutes
    timothy_end = (21 - 9) * 60 + 30    # 21:30 -> 750 minutes

    # Define variables (in minutes since 9:00 AM)
    leave_Alamo = Int('leave_Alamo')
    start_meet = leave_Alamo + 12  # travel time to Richmond
    end_meet = start_meet + 45     # meeting duration is 45 minutes

    s = Solver()
    # Constraints
    s.add(leave_Alamo >= 0)                # Cannot leave before 9:00 AM
    s.add(start_meet >= timothy_start)      # Meeting starts at or after 20:45
    s.add(end_meet <= timothy_end)          # Meeting ends by 21:30

    if s.check() == sat:
        m = s.model()
        leave_val = m[leave_Alamo].as_long()
        start_val = leave_val + 12
        end_val = start_val + 45

        # Convert minutes to HH:MM format
        def format_time(total_minutes):
            hours = 9 + total_minutes // 60
            minutes = total_minutes % 60
            return f"{hours:02d}:{minutes:02d}"

        start_str = format_time(start_val)
        end_str = format_time(end_val)

        itinerary = [{
            "action": "meet",
            "person": "Timothy",
            "start_time": start_str,
            "end_time": end_str
        }]
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()