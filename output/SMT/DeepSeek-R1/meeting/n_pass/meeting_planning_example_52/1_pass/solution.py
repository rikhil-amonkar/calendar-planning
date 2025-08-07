from z3 import *
import json

def main():
    # Convert time to minutes from 9:00 AM
    t_depart = Int('t_depart')  # departure time from Russian Hill
    s = Int('s')                # meeting start time

    opt = Optimize()
    # Constraints
    opt.add(t_depart >= 0)  # departure time must be after 9:00 AM
    opt.add(s >= t_depart + 14)  # travel time constraint
    opt.add(s >= 255)  # meeting must start at or after 1:15 PM
    opt.add(s + 45 <= 555)  # meeting must end by 6:15 PM

    # Minimize meeting start time to free up the day
    opt.minimize(s)

    if opt.check() == sat:
        m = opt.model()
        s_val = m[s].as_long()
        e_val = s_val + 45  # meeting end time

        # Convert minutes to HH:MM format
        start_hour = 9 + s_val // 60
        start_minute = s_val % 60
        end_hour = 9 + e_val // 60
        end_minute = e_val % 60

        start_time = f"{start_hour:02d}:{start_minute:02d}"
        end_time = f"{end_hour:02d}:{end_minute:02d}"

        # Create itinerary
        itinerary = [{
            "action": "meet",
            "person": "Barbara",
            "start_time": start_time,
            "end_time": end_time
        }]

        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        # No feasible solution
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()