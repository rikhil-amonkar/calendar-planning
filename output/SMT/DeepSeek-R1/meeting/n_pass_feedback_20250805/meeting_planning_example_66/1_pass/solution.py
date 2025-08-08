from z3 import *
import json

def main():
    s = Solver()
    depart_NobHill = Int('depart_NobHill')
    start_meet = Int('start_meet')
    end_meet = Int('end_meet')

    # Constraints
    s.add(depart_NobHill >= 0)
    s.add(start_meet >= depart_NobHill + 17)
    s.add(start_meet >= 135)  # 11:15 AM in minutes from 9:00
    s.add(end_meet == start_meet + 120)
    s.add(end_meet <= 525)   # 5:45 PM in minutes from 9:00

    # Minimize the meeting start time
    s.minimize(start_meet)

    if s.check() == sat:
        m = s.model()
        start_val = m.eval(start_meet).as_long()
        end_val = start_val + 120

        # Convert to time string
        start_hour = 9 + start_val // 60
        start_min = start_val % 60
        end_hour = 9 + end_val // 60
        end_min = end_val % 60

        # Format to HH:MM
        start_time = f"{start_hour:02d}:{start_min:02d}"
        end_time = f"{end_hour:02d}:{end_min:02d}"

        meeting_entry = {
            "action": "meet",
            "person": "Robert",
            "start_time": start_time,
            "end_time": end_time
        }

        result = {"itinerary": [meeting_entry]}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()