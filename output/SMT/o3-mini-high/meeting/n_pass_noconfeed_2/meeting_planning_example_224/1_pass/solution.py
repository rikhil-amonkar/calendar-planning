import json
from z3 import *

def main():
    # Initialize the Z3 solver
    solver = Solver()
    
    # Decision variables for meeting times (in minutes after midnight)
    # Melissa meeting at Golden Gate Park
    M_start = Int('M_start')
    M_end   = Int('M_end')
    # Emily meeting at Richmond District
    E_start = Int('E_start')
    E_end   = Int('E_end')
    # Nancy meeting at Presidio
    N_start = Int('N_start')
    N_end   = Int('N_end')
    
    # Constants: times in minutes after midnight
    fishermans_wharf_arrival = 9 * 60        # 9:00 AM = 540 minutes
    travel_FW_to_GGP = 25                    # Minutes from Fisherman's Wharf to Golden Gate Park
    travel_GGP_to_RD = 7                     # Minutes from Golden Gate Park to Richmond District
    travel_RD_to_Presidio = 7                # Minutes from Richmond District to Presidio
    
    # Availability windows (in minutes after midnight)
    # Melissa at Golden Gate Park: 8:30 AM to 8:00 PM
    melissa_avail_start = 8 * 60 + 30          # 510
    melissa_avail_end   = 20 * 60              # 1200
    # Emily at Richmond District: 4:45 PM to 10:00 PM
    emily_avail_start = 16 * 60 + 45           # 1005
    emily_avail_end   = 22 * 60                # 1320
    # Nancy at Presidio: 7:45 PM to 10:00 PM
    nancy_avail_start = 19 * 60 + 45           # 1185
    nancy_avail_end   = 22 * 60                # 1320
    
    # Minimum meeting durations (in minutes)
    melissa_min_duration = 15
    emily_min_duration = 120
    nancy_min_duration = 105
    
    # Constraints for Melissa meeting at Golden Gate Park:
    # Arrival at Fisherman's Wharf is at 9:00, plus travel time 25 minutes.
    solver.add(M_start >= fishermans_wharf_arrival + travel_FW_to_GGP)
    solver.add(M_start >= melissa_avail_start)  # Must be within Melissa's available window
    solver.add(M_end <= melissa_avail_end)
    solver.add(M_end - M_start >= melissa_min_duration)
    
    # Constraints for Emily meeting at Richmond District:
    # After Melissa meeting, travel from Golden Gate Park to Richmond District takes 7 minutes.
    solver.add(E_start >= M_end + travel_GGP_to_RD)
    solver.add(E_start >= emily_avail_start)
    solver.add(E_end <= emily_avail_end)
    solver.add(E_end - E_start >= emily_min_duration)
    
    # Constraints for Nancy meeting at Presidio:
    # After Emily meeting, travel from Richmond District to Presidio takes 7 minutes.
    solver.add(N_start >= E_end + travel_RD_to_Presidio)
    solver.add(N_start >= nancy_avail_start)
    solver.add(N_end <= nancy_avail_end)
    solver.add(N_end - N_start >= nancy_min_duration)
    
    # Check for a valid schedule
    if solver.check() == sat:
        model = solver.model()
        M_start_val = model[M_start].as_long()
        M_end_val = model[M_end].as_long()
        E_start_val = model[E_start].as_long()
        E_end_val = model[E_end].as_long()
        N_start_val = model[N_start].as_long()
        N_end_val = model[N_end].as_long()
        
        # Helper function to convert minutes into H:MM 24-hour format
        def format_time(minutes):
            hour = minutes // 60
            minute = minutes % 60
            return f"{hour}:{minute:02d}"
        
        itinerary = [
            {
                "action": "meet",
                "location": "Golden Gate Park",
                "person": "Melissa",
                "start_time": format_time(M_start_val),
                "end_time": format_time(M_end_val)
            },
            {
                "action": "meet",
                "location": "Richmond District",
                "person": "Emily",
                "start_time": format_time(E_start_val),
                "end_time": format_time(E_end_val)
            },
            {
                "action": "meet",
                "location": "Presidio",
                "person": "Nancy",
                "start_time": format_time(N_start_val),
                "end_time": format_time(N_end_val)
            }
        ]
        
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        # In case there is no valid schedule, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()