from z3 import *
import json

def main():
    opt = Optimize()
    depart_NobHill = Int('depart_NobHill')
    start_meet = Int('start_meet')

    # Constraints
    opt.add(depart_NobHill >= 0)
    opt.add(start_meet >= depart_NobHill + 17)
    opt.add(start_meet >= 135)  # 11:15 AM in minutes from 9:00
    opt.add(start_meet + 120 <= 525)   # 5:45 PM in minutes from 9:00

    # Minimize the meeting start time
    opt.minimize(start_meet)

    if opt.check() == sat:
        m = opt.model()
        start_val = m.eval(start_meet).as_long()
        end_val = start_val + 120

        # Convert to time string
        base_hour = 9
        start_hour = base_hour + start_val // 60
        start_min = start_val % 60
        end_hour = base_hour + end_val // 60
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