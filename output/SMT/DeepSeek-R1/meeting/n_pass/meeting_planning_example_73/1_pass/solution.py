from z3 import *
import json

def main():
    # Convert times to minutes from midnight
    min_start = 9 * 60 + 7  # 9:07 AM (547 minutes)
    max_end = 22 * 60       # 10:00 PM (1320 minutes)

    s = Optimize()
    start_b = Int('start_b')
    s.add(start_b >= min_start)
    s.add(start_b + 60 <= max_end)
    s.minimize(start_b)

    if s.check() == sat:
        m = s.model()
        start_val = m[start_b].as_long()
        end_val = start_val + 60

        start_hour = start_val // 60
        start_minute = start_val % 60
        end_hour = end_val // 60
        end_minute = end_val % 60

        start_time = f"{start_hour:02d}:{start_minute:02d}"
        end_time = f"{end_hour:02d}:{end_minute:02d}"

        meeting = {
            "action": "meet",
            "person": "Barbara",
            "start_time": start_time,
            "end_time": end_time
        }
        result = {"itinerary": [meeting]}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()