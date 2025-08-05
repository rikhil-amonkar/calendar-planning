from z3 import *
import json

def main():
    T_start = Int('T_start')
    P_start = Int('P_start')
    A_start = Int('A_start')
    
    s = Solver()
    
    # Convert times to minutes since midnight
    start_location_time = 540  # 9:00 AM
    timothy_available_start = 585  # 9:45 AM
    timothy_available_end = 1065  # 5:45 PM
    patricia_available_start = 1110  # 6:30 PM
    patricia_available_end = 1305  # 9:45 PM
    ashley_available_start = 1230  # 8:30 PM
    ashley_available_end = 1275  # 9:15 PM
    
    # Travel times in minutes
    travel_russian_to_embarcadero = 8
    travel_embarcadero_to_nob = 10
    travel_nob_to_mission = 13
    
    # Meeting durations in minutes
    duration_timothy = 120
    duration_patricia = 90
    duration_ashley = 45
    
    # Constraints for Timothy
    s.add(T_start >= timothy_available_start)
    s.add(T_start + duration_timothy <= timothy_available_end)
    s.add(T_start >= start_location_time + travel_russian_to_embarcadero)
    
    # Constraints for Patricia
    s.add(P_start >= T_start + duration_timothy + travel_embarcadero_to_nob)
    s.add(P_start >= patricia_available_start)
    s.add(P_start + duration_patricia <= patricia_available_end)
    
    # Constraints for Ashley
    s.add(A_start == ashley_available_start)  # Must start at 8:30 PM
    s.add(A_start + duration_ashley <= ashley_available_end)
    s.add(A_start >= P_start + duration_patricia + travel_nob_to_mission)
    
    if s.check() == sat:
        m = s.model()
        t_val = m.eval(T_start).as_long()
        p_val = m.eval(P_start).as_long()
        a_val = m.eval(A_start).as_long()
        
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"
        
        itinerary = [
            {"action": "meet", "person": "Timothy", "start_time": format_time(t_val), "end_time": format_time(t_val + duration_timothy)},
            {"action": "meet", "person": "Patricia", "start_time": format_time(p_val), "end_time": format_time(p_val + duration_patricia)},
            {"action": "meet", "person": "Ashley", "start_time": format_time(a_val), "end_time": format_time(a_val + duration_ashley)}
        ]
        
        # Sort by start_time
        itinerary_sorted = sorted(itinerary, key=lambda x: x['start_time'])
        result = {"itinerary": itinerary_sorted}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()