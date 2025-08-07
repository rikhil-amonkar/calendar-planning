from z3 import *
import json

def main():
    # Initialize the optimizer
    opt = Optimize()
    
    # Define variables (in minutes from 9:00 AM)
    T0 = Int('T0')  # Departure time from Nob Hill
    s = Int('s')    # Meeting start time
    e = Int('e')    # Meeting end time
    
    # Travel time from Nob Hill to Presidio
    travel_time = 17
    
    # Convert time constraints to minutes from 9:00 AM
    robert_start = 135  # 11:15 AM (2h15m after 9:00 AM)
    robert_end = 525    # 5:45 PM (8h45m after 9:00 AM)
    
    # Constraints:
    opt.add(T0 >= 0)  # Cannot leave Nob Hill before 9:00 AM
    opt.add(s >= T0 + travel_time)  # Meeting starts after arrival at Presidio
    opt.add(s >= robert_start)      # Meeting starts no earlier than Robert's availability
    opt.add(e <= robert_end)        # Meeting ends no later than Robert's availability
    opt.add(e - s >= 120)           # Meeting lasts at least 120 minutes
    
    # Maximize the meeting duration
    opt.maximize(e - s)
    
    if opt.check() == sat:
        model = opt.model()
        s_val = model[s].as_long()
        e_val = model[e].as_long()
        
        # Convert minutes to time string (from 9:00 AM base)
        def min_to_time(mins):
            total_mins = 9 * 60 + mins
            hours = total_mins // 60
            minutes = total_mins % 60
            return f"{hours:02d}:{minutes:02d}"
        
        start_time = min_to_time(s_val)
        end_time = min_to_time(e_val)
        
        # Create itinerary
        itinerary = [
            {"action": "meet", "person": "Robert", "start_time": start_time, "end_time": end_time}
        ]
        
        # Output JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')  # Fallback if no solution found

if __name__ == "__main__":
    main()