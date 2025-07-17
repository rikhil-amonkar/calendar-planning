from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Time variables in minutes since 9:00 AM (540 minutes)
    # Meeting Jason
    jason_start = Int('jason_start')  # minutes from 9:00 AM
    jason_end = Int('jason_end')
    
    # Meeting Kenneth
    kenneth_start = Int('kenneth_start')
    kenneth_end = Int('kenneth_end')
    
    # Travel times
    ph_to_presidio = 11
    ph_to_marina = 6
    presidio_to_marina = 10
    marina_to_presidio = 10
    marina_to_ph = 7
    presidio_to_ph = 11
    
    # Jason's availability: 10:00 AM (60 minutes after 9:00 AM) to 4:15 PM (435 minutes)
    s.add(jason_start >= 60)
    s.add(jason_end <= 435)
    s.add(jason_end - jason_start >= 90)
    
    # Kenneth's availability: 3:30 PM (390 minutes) to 4:45 PM (465 minutes)
    s.add(kenneth_start >= 390)
    s.add(kenneth_end <= 465)
    s.add(kenneth_end - kenneth_start >= 45)
    
    # Starting at Pacific Heights at 9:00 AM (time 0)
    
    # Possible scenarios:
    # Option 1: Meet Jason first, then Kenneth
    # Travel from PH to Presidio: 11 minutes
    # Then from Presidio to Marina: 10 minutes
    # So jason_start >= 11 (since starting at 0)
    # kenneth_start >= jason_end + 10
    
    # Option 2: Meet Kenneth first, then Jason
    # Travel from PH to Marina: 6 minutes
    # Then from Marina to Presidio: 10 minutes
    # So kenneth_start >= 6
    # jason_start >= kenneth_end + 10
    
    # We need to model both options and see which one is feasible
    
    # Create a flag to choose between options
    option = Int('option')
    s.add(Or(option == 1, option == 2))
    
    # Option 1: Jason first
    s.add(Implies(option == 1, jason_start >= 11))
    s.add(Implies(option == 1, kenneth_start >= jason_end + presidio_to_marina))
    
    # Option 2: Kenneth first
    s.add(Implies(option == 2, kenneth_start >= 6))
    s.add(Implies(option == 2, jason_start >= kenneth_end + marina_to_presidio))
    
    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        opt = m[option].as_long()
        
        # Convert times to HH:MM format
        def minutes_to_time(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes in 24-hour format
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{hours:02d}:{mins:02d}"
        
        itinerary = []
        
        if opt == 1:
            js_start = m[jason_start].as_long()
            js_end = m[jason_end].as_long()
            ks_start = m[kenneth_start].as_long()
            ks_end = m[kenneth_end].as_long()
            
            itinerary.append({
                "action": "meet",
                "person": "Jason",
                "start_time": minutes_to_time(js_start),
                "end_time": minutes_to_time(js_end)
            })
            itinerary.append({
                "action": "meet",
                "person": "Kenneth",
                "start_time": minutes_to_time(ks_start),
                "end_time": minutes_to_time(ks_end)
            })
        else:
            ks_start = m[kenneth_start].as_long()
            ks_end = m[kenneth_end].as_long()
            js_start = m[jason_start].as_long()
            js_end = m[jason_end].as_long()
            
            itinerary.append({
                "action": "meet",
                "person": "Kenneth",
                "start_time": minutes_to_time(ks_start),
                "end_time": minutes_to_time(ks_end)
            })
            itinerary.append({
                "action": "meet",
                "person": "Jason",
                "start_time": minutes_to_time(js_start),
                "end_time": minutes_to_time(js_end)
            })
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Execute and print the solution
solution = solve_scheduling()
print(solution)