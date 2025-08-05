from z3 import *

def main():
    # Initialize the solver
    s = Solver()
    
    # Define the start times in minutes from midnight
    start_P = Int('start_P')  # Patricia's start time
    start_R = Int('start_R')  # Ronald's start time
    start_E = Int('start_E')  # Emily's start time
    
    # Constraints for Patricia
    s.add(start_P >= 540 + 31)  # Travel from FD to SD: 31 minutes
    s.add(start_P <= 750 - 60 - 29)  # Must arrive at Laura by 12:30 PM (750 minutes)
    s.add(start_P + 60 <= 1320)  # Patricia's availability ends at 10:00 PM (1320 minutes)
    s.add(start_P >= 555)  # Patricia's availability starts at 9:15 AM (555 minutes)
    
    # Constraints for Ronald
    s.add(start_R >= 825)  # Ronald's availability starts at 1:45 PM (825 minutes)
    s.add(start_R + 105 <= 1035)  # Ronald's availability ends at 5:15 PM (1035 minutes)
    s.add(start_R >= 765 + 4)  # Travel from Laura (NB) to Ronald (RH): 4 minutes
    
    # Constraints for Emily
    s.add(start_E >= 975)  # Emily's availability starts at 4:15 PM (975 minutes)
    s.add(start_E + 60 <= 1110)  # Emily's availability ends at 6:30 PM (1110 minutes)
    s.add(start_E >= start_R + 105 + 21)  # Travel from Ronald (RH) to Emily (TC): 21 minutes
    
    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        start_P_val = m.eval(start_P).as_long()
        start_R_val = m.eval(start_R).as_long()
        start_E_val = m.eval(start_E).as_long()
        
        # Convert minutes to HH:MM format
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"
        
        # Define the itinerary in chronological order
        itinerary = [
            {"action": "meet", "person": "Patricia", "start_time": format_time(start_P_val), "end_time": format_time(start_P_val + 60)},
            {"action": "meet", "person": "Laura", "start_time": "12:30", "end_time": "12:45"},
            {"action": "meet", "person": "Ronald", "start_time": format_time(start_R_val), "end_time": format_time(start_R_val + 105)},
            {"action": "meet", "person": "Emily", "start_time": format_time(start_E_val), "end_time": format_time(start_E_val + 60)}
        ]
        
        # Output the itinerary as a JSON-formatted dictionary
        print('SOLUTION:')
        print('{"itinerary": ' + str(itinerary).replace("'", '"') + '}')
    else:
        print("No solution found")

if __name__ == "__main__":
    main()