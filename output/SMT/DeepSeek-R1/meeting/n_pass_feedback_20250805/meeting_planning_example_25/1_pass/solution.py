import z3
import json

def main():
    # Convert all times to minutes since midnight
    start_of_day = 9 * 60  # 9:00 AM
    david_start = 16 * 60  # 4:00 PM
    david_end = 21 * 60 + 45  # 9:45 PM
    travel_time = 23  # minutes

    # Define Z3 integer variables
    T = z3.Int('T')  # Departure time from Golden Gate Park
    S = z3.Int('S')  # Meeting start time with David
    E = z3.Int('E')  # Meeting end time with David

    # Initialize the optimizer
    opt = z3.Optimize()
    
    # Constraints:
    opt.add(T >= start_of_day)  # Departure after 9:00 AM
    opt.add(T + travel_time <= S)  # Arrive by meeting start time
    opt.add(S >= david_start)  # Meeting starts when David is available
    opt.add(E == S + 105)      # Meeting lasts exactly 105 minutes
    opt.add(E <= david_end)    # Meeting ends before David leaves
    
    # Minimize the meeting start time to free up the day
    opt.minimize(S)
    
    # Check for a solution
    if opt.check() == z3.sat:
        model = opt.model()
        S_val = model[S].as_long()
        E_val = model[E].as_long()
        
        # Convert minutes back to HH:MM format
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"
        
        meeting = {
            "action": "meet",
            "person": "David",
            "start_time": format_time(S_val),
            "end_time": format_time(E_val)
        }
        result = {"itinerary": [meeting]}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        # Handle unsat case (should not happen with given constraints)
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()