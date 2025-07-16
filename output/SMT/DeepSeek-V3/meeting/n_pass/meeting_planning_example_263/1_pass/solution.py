from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define variables for meeting start and end times
    # Meeting with Karen at Fisherman's Wharf
    karen_start = Int('karen_start')
    karen_end = Int('karen_end')
    
    # Meeting with Anthony at Financial District
    anthony_start = Int('anthony_start')
    anthony_end = Int('anthony_end')
    
    # Meeting with Betty at Embarcadero
    betty_start = Int('betty_start')
    betty_end = Int('betty_end')
    
    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    arrival_time = 540  # 9:00 AM is 540 minutes since midnight
    
    # Friends' availability windows in minutes since midnight
    # Betty: 7:45 PM to 9:45 PM (1170 to 1305)
    betty_available_start = 1170
    betty_available_end = 1305
    
    # Karen: 8:45 AM to 3:00 PM (525 to 900)
    karen_available_start = 525
    karen_available_end = 900
    
    # Anthony: 9:15 AM to 9:30 PM (555 to 1350)
    anthony_available_start = 555
    anthony_available_end = 1350
    
    # Minimum meeting durations in minutes
    karen_min_duration = 30
    anthony_min_duration = 105
    betty_min_duration = 15
    
    # Travel times in minutes
    # From Bayview to Fisherman's Wharf: 25
    bayview_to_fisherman = 25
    # From Fisherman's Wharf to Financial District: 11
    fisherman_to_financial = 11
    # From Financial District to Embarcadero: 4
    financial_to_embarcadero = 4
    # From Embarcadero to Bayview: 21 (not needed for return)
    
    # Constraints for Karen (Fisherman's Wharf)
    s.add(karen_start >= karen_available_start)
    s.add(karen_end <= karen_available_end)
    s.add(karen_end - karen_start >= karen_min_duration)
    # You start at Bayview at 540 (9:00 AM), travel to Fisherman's Wharf takes 25 minutes
    s.add(karen_start >= arrival_time + bayview_to_fisherman)
    
    # Constraints for Anthony (Financial District)
    s.add(anthony_start >= anthony_available_start)
    s.add(anthony_end <= anthony_available_end)
    s.add(anthony_end - anthony_start >= anthony_min_duration)
    # After meeting Karen, travel to Financial District takes 11 minutes
    s.add(anthony_start >= karen_end + fisherman_to_financial)
    
    # Constraints for Betty (Embarcadero)
    s.add(betty_start >= betty_available_start)
    s.add(betty_end <= betty_available_end)
    s.add(betty_end - betty_start >= betty_min_duration)
    # After meeting Anthony, travel to Embarcadero takes 4 minutes
    s.add(betty_start >= anthony_end + financial_to_embarcadero)
    
    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        # Convert times back to human-readable format
        def minutes_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h}:{m:02d}"
        
        karen_s = m.evaluate(karen_start).as_long()
        karen_e = m.evaluate(karen_end).as_long()
        anthony_s = m.evaluate(anthony_start).as_long()
        anthony_e = m.evaluate(anthony_end).as_long()
        betty_s = m.evaluate(betty_start).as_long()
        betty_e = m.evaluate(betty_end).as_long()
        
        print("SOLUTION:")
        print(f"Meet Karen at Fisherman's Wharf from {minutes_to_time(karen_s)} to {minutes_to_time(karen_e)}")
        print(f"Meet Anthony at Financial District from {minutes_to_time(anthony_s)} to {minutes_to_time(anthony_e)}")
        print(f"Meet Betty at Embarcadero from {minutes_to_time(betty_s)} to {minutes_to_time(betty_e)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()