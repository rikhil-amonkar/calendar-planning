import z3
import json

def main():
    solver = z3.Solver()

    # Define variables
    T1 = z3.Int('T1')  # Departure time from Fisherman's Wharf (minutes since midnight)
    S = z3.Int('S')    # Start time of meeting with Kenneth
    E = z3.Int('E')    # End time of meeting with Kenneth

    # Constraints
    # 1. You arrive at Fisherman's Wharf at 9:00AM (540 minutes)
    #    and can leave anytime after that
    solver.add(T1 >= 540)
    
    # 2. Travel time from Fisherman's Wharf to Nob Hill is 11 minutes
    #    You must arrive at Nob Hill before the meeting starts
    solver.add(T1 + 11 <= S)
    
    # 3. Kenneth is available from 2:15PM (855 minutes) to 7:45PM (1185 minutes)
    solver.add(S >= 855)
    solver.add(E <= 1185)
    
    # 4. Meeting must last at least 90 minutes
    solver.add(E == S + 90)

    # Check for solution
    if solver.check() == z3.sat:
        model = solver.model()
        s_val = model[S].as_long()
        e_val = model[E].as_long()
        
        # Convert minutes to H:MM format
        def to_time_str(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours}:{mins:02d}"
        
        itinerary = [
            {
                "action": "meet",
                "location": "Nob Hill",
                "person": "Kenneth",
                "start_time": to_time_str(s_val),
                "end_time": to_time_str(e_val)
            }
        ]
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()