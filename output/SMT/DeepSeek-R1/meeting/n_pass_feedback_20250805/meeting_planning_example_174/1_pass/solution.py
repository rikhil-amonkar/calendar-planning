from z3 import *
import json

def format_time(minutes):
    total_minutes = minutes
    hours_component = total_minutes // 60
    mins_component = total_minutes % 60
    absolute_hour = 9 + hours_component
    return f"{absolute_hour:02d}:{mins_component:02d}"

def main():
    k_start = Int('k_start')
    k_duration = Int('k_duration')
    
    s = Optimize()
    s.add(k_start >= 180)  # Kenneth available from 12:00 (180 minutes from 9:00)
    s.add(k_duration >= 45)  # Minimum meeting time with Kenneth
    s.add(k_start + k_duration <= 405)  # Kenneth available until 15:45 (405 minutes)
    s.add(k_start + k_duration >= 374)  # To ensure Thomas meeting starts at 390 (3:30 PM) after travel

    s.minimize(k_start)

    if s.check() == sat:
        m = s.model()
        k_start_val = m[k_start].as_long()
        k_duration_val = m[k_duration].as_long()
        k_end_val = k_start_val + k_duration_val
        
        # Thomas meeting starts after travel from Kenneth's meeting
        t_start_val = k_end_val + 16  # Travel time from Mission to Pacific Heights
        t_duration_val = 75  # Minimum meeting time with Thomas
        t_end_val = t_start_val + t_duration_val
        
        # Format times
        ken_start_str = format_time(k_start_val)
        ken_end_str = format_time(k_end_val)
        thomas_start_str = format_time(t_start_val)
        thomas_end_str = format_time(t_end_val)
        
        itinerary = [
            {"action": "meet", "person": "Kenneth", "start_time": ken_start_str, "end_time": ken_end_str},
            {"action": "meet", "person": "Thomas", "start_time": thomas_start_str, "end_time": thomas_end_str}
        ]
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()