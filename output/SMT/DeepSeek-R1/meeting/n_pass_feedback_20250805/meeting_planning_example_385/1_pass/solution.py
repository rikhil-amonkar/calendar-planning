from z3 import *

def main():
    # Initialize Z3 solver
    s = Solver()
    
    # Travel times matrix: [Nob_Hill, Presidio, North_Beach, Fisherman_Wharf, Pacific_Heights]
    travel_time = [
        [0, 17, 8, 11, 8],    # From Nob Hill
        [18, 0, 18, 19, 11],   # From Presidio
        [7, 17, 0, 5, 8],      # From North Beach
        [11, 17, 6, 0, 12],    # From Fisherman's Wharf
        [8, 11, 9, 13, 0]      # From Pacific Heights
    ]
    
    # Convert time to minutes from midnight
    def time_to_minutes(time_str):
        h, m = time_str.split(':')
        return int(h) * 60 + int(m)
    
    # Start at Nob Hill (location 0) at 9:00 AM (540 minutes)
    start0 = 540
    end0 = 540
    
    # Friend indices: John (4), Steven (2), Barbara (3)
    # John at Pacific Heights (4): available 9:00 AM (540) to 1:30 PM (810)
    start4 = end0 + travel_time[0][4]  # 540 + 8 = 548 minutes (9:08 AM)
    duration4 = Int('duration4')
    s.add(duration4 >= 15)  # Minimum 15 minutes
    end4 = start4 + duration4
    s.add(end4 <= 810)  # John must finish by 1:30 PM (810 minutes)
    
    # Travel to Steven at North Beach (2): travel time = 9 minutes
    arrival2 = end4 + travel_time[4][2]  # End of John + travel
    start2 = Int('start2')
    # Steven available from 1:30 PM (810 minutes), so start2 is max(arrival2, 810)
    s.add(start2 == If(arrival2 >= 810, arrival2, 810))
    duration2 = Int('duration2')
    s.add(duration2 >= 45)  # Minimum 45 minutes
    end2 = start2 + duration2
    s.add(end2 <= 1320)  # Steven available until 10:00 PM (1320 minutes)
    
    # Travel to Barbara at Fisherman's Wharf (3): travel time = 5 minutes
    arrival3 = end2 + travel_time[2][3]  # End of Steven + travel
    start3 = Int('start3')
    # Barbara available from 6:00 PM (1080 minutes), so start3 is max(arrival3, 1080)
    s.add(start3 == If(arrival3 >= 1080, arrival3, 1080))
    duration3 = Int('duration3')
    s.add(duration3 >= 30)  # Minimum 30 minutes
    end3 = start3 + duration3
    s.add(end3 <= 1290)  # Barbara available until 9:30 PM (1290 minutes)
    
    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        dur4_val = model.eval(duration4).as_long()
        end4_val = start4 + dur4_val
        start2_val = model.eval(start2).as_long()
        dur2_val = model.eval(duration2).as_long()
        end2_val = start2_val + dur2_val
        start3_val = model.eval(start3).as_long()
        dur3_val = model.eval(duration3).as_long()
        end3_val = start3_val + dur3_val
        
        # Convert times to HH:MM
        def minutes_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"
        
        itinerary = [
            {"action": "meet", "person": "John", "start_time": minutes_to_time(start4), "end_time": minutes_to_time(end4_val)},
            {"action": "meet", "person": "Steven", "start_time": minutes_to_time(start2_val), "end_time": minutes_to_time(end2_val)},
            {"action": "meet", "person": "Barbara", "start_time": minutes_to_time(start3_val), "end_time": minutes_to_time(end3_val)}
        ]
        
        # Output the itinerary in JSON format
        print('SOLUTION:')
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()