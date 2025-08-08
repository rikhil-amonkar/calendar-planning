from z3 import *
import json

def main():
    def time_to_minutes(time_str):
        h, m = time_str.split(':')
        return int(h) * 60 + int(m)
    
    def minutes_to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"
    
    # Initial arrival at Russian Hill
    arrival_time = time_to_minutes("09:00")
    travel_time = 7
    min_meeting_duration = 60
    barbara_start = time_to_minutes("07:15")
    barbara_end = time_to_minutes("22:00")
    
    opt = Optimize()
    meet_start = Int('meet_start')
    meet_end = meet_start + min_meeting_duration
    
    opt.add(meet_start >= arrival_time + travel_time)
    opt.add(meet_start >= barbara_start)
    opt.add(meet_end <= barbara_end)
    
    opt.minimize(meet_start)
    
    if opt.check() == sat:
        m = opt.model()
        start_min = m[meet_start].as_long()
        end_min = start_min + min_meeting_duration
        start_str = minutes_to_time(start_min)
        end_str = minutes_to_time(end_min)
        
        itinerary = [
            {"action": "meet", "person": "Barbara", "start_time": start_str, "end_time": end_str}
        ]
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()