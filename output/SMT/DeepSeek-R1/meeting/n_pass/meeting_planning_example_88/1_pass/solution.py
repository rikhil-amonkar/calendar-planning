from z3 import *
import json

def main():
    # Convert time to minutes since midnight
    start_minutes = 9 * 60  # 9:00 AM
    joshua_start_minutes = 20 * 60 + 45  # 20:45
    joshua_end_minutes = 21 * 60 + 45    # 21:45

    # Declare Z3 variables
    T = Int('T')  # Departure time from Sunset District (minutes from midnight)
    S = Int('S')  # Meeting start time
    E = Int('E')  # Meeting end time

    opt = Optimize()
    
    # Constraints
    opt.add(T >= start_minutes)  # Depart after 9:00 AM
    arrival = T + 11             # Travel time to Golden Gate Park
    opt.add(S >= arrival)        # Meeting starts after arrival
    opt.add(S >= joshua_start_minutes)  # Meeting starts no earlier than 20:45
    opt.add(E <= joshua_end_minutes)    # Meeting ends no later than 21:45
    opt.add(E - S >= 15)         # Meeting lasts at least 15 minutes

    # Maximize the meeting duration
    opt.maximize(E - S)
    
    if opt.check() == sat:
        model = opt.model()
        S_val = model[S].as_long()
        E_val = model[E].as_long()
        
        # Format time to HH:MM
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"
        
        start_str = format_time(S_val)
        end_str = format_time(E_val)
        
        itinerary = {
            "itinerary": [
                {
                    "action": "meet",
                    "person": "Joshua",
                    "start_time": start_str,
                    "end_time": end_str
                }
            ]
        }
        print(json.dumps(itinerary))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()