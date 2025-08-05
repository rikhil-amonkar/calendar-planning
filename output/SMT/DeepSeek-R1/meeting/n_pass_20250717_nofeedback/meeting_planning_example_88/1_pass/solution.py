from z3 import *

def main():
    # Convert times to minutes
    start_of_day = 9 * 60  # 9:00 AM in minutes since midnight
    joshua_start = 20 * 60 + 45  # 20:45
    joshua_end = 21 * 60 + 45    # 21:45

    # Create solver
    s = Optimize()

    # Variables for the meeting with Joshua
    start = Int('start')
    duration = Int('duration')
    end = start + duration

    # Constraints
    s.add(start >= joshua_start)
    s.add(end <= joshua_end)
    s.add(duration >= 15)
    s.add(start - 11 >= start_of_day)  # travel time from Sunset to GGP is 11 minutes

    # Objective: maximize the duration
    s.maximize(duration)

    if s.check() == sat:
        m = s.model()
        start_val = m.eval(start).as_long()
        duration_val = m.eval(duration).as_long()
        end_val = start_val + duration_val

        # Convert back to HH:MM
        def to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        start_str = to_time(start_val)
        end_str = to_time(end_val)

        # Create the itinerary
        itinerary = [
            {"action": "meet", "person": "Joshua", "start_time": start_str, "end_time": end_str}
        ]

        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()