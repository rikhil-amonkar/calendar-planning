from z3 import *
import json

def main():
    # Time in minutes since 9:00 AM
    S = Int('S')  # Meeting start time
    E = Int('E')  # Meeting end time
    
    opt = Optimize()
    # Kenneth is available from 14:15 (315 minutes after 9:00 AM) to 19:45 (645 minutes after 9:00 AM)
    opt.add(S >= 315)
    opt.add(E <= 645)
    opt.add(E - S >= 90)  # Minimum meeting duration
    
    # Maximize the meeting duration
    opt.maximize(E - S)
    
    if opt.check() == sat:
        m = opt.model()
        start_minutes = m[S].as_long()
        end_minutes = m[E].as_long()
        
        # Convert minutes since 9:00 AM to 24-hour time
        start_total_minutes = 9 * 60 + start_minutes
        start_hour = start_total_minutes // 60
        start_minute = start_total_minutes % 60
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        
        end_total_minutes = 9 * 60 + end_minutes
        end_hour = end_total_minutes // 60
        end_minute = end_total_minutes % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        meeting = {
            "action": "meet",
            "person": "Kenneth",
            "start_time": start_time,
            "end_time": end_time
        }
        result = {"itinerary": [meeting]}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()