from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()
    
    # Convert all times to minutes since 9:00 AM (540 minutes)
    # Laura's availability: 12:15 PM to 7:45 PM (735 to 1170 minutes since midnight)
    # Anthony's availability: 12:30 PM to 2:45 PM (750 to 885 minutes since midnight)
    # Since we start at 9:00 AM (540 minutes), we'll adjust all times relative to 9:00 AM.
    # So Laura's availability: 12:15 PM is 3*60 + 15 = 195 minutes after 9:00 AM.
    # Anthony's availability: 12:30 PM is 3*60 + 30 = 210 minutes after 9:00 AM.
    
    # Meeting start and end times (relative to 9:00 AM)
    meet_laura_start = Int('meet_laura_start')
    meet_laura_end = Int('meet_laura_end')
    meet_anthony_start = Int('meet_anthony_start')
    meet_anthony_end = Int('meet_anthony_end')
    
    # Laura's availability: 195 to 675 minutes after 9:00 AM (12:15 PM to 7:45 PM is 3h15m to 10h45m after 9:00 AM)
    laura_start_min = 195
    laura_end_max = 675  # 7:45 PM is 10h45m after 9:00 AM (10*60 + 45 = 645? Wait no: 12:15 PM is 3h15m after 9:00 AM, 7:45 PM is 10h45m after 9:00 AM. So 10*60 +45=645. So laura_end_max is 645.
    # Correction: 12:15 PM is 3h15m after 9:00 AM (195 minutes), 7:45 PM is 10h45m after 9:00 AM (645 minutes).
    
    # Anthony's availability: 210 to 285 minutes after 9:00 AM (12:30 PM to 2:45 PM is 3h30m to 5h45m after 9:00 AM)
    anthony_start_min = 210
    anthony_end_max = 285  # 2:45 PM is 5h45m after 9:00 AM (5*60 +45=345 minutes? Wait no: 12:30 PM is 3h30m (210 minutes), 2:45 PM is 5h45m (345 minutes). So anthony_end_max is 345.
    # Wait, the original note says Anthony is available from 12:30 PM to 2:45 PM. So 12:30 PM is 3h30m after 9:00 AM (210 minutes), 2:45 PM is 5h45m after 9:00 AM (345 minutes). So anthony_end_max is 345.
    
    # Meeting duration constraints
    s.add(meet_laura_end == meet_laura_start + 75)  # Laura's meeting lasts 75 minutes
    s.add(meet_anthony_end == meet_anthony_start + 30)  # Anthony's meeting lasts 30 minutes
    
    # Availability constraints
    s.add(meet_laura_start >= laura_start_min)
    s.add(meet_laura_end <= laura_end_max)
    s.add(meet_anthony_start >= anthony_start_min)
    s.add(meet_anthony_end <= anthony_end_max)
    
    # Travel times
    # The Castro to Mission District: 7 minutes
    # The Castro to Financial District: 20 minutes
    # Mission District to Financial District: 17 minutes
    # Financial District to Mission District: 17 minutes
    
    # We start at The Castro at time 0 (9:00 AM).
    # We need to schedule the meetings with Laura and Anthony, possibly with travel in between.
    
    # There are two possible orders:
    # 1. Meet Anthony first, then Laura.
    # 2. Meet Laura first, then Anthony.
    
    # We'll create two separate scenarios and let Z3 choose the feasible one.
    
    # Scenario 1: Meet Anthony first, then Laura.
    scenario1 = And(
        meet_anthony_start >= 20,  # Travel from Castro to Financial District takes 20 minutes.
        meet_laura_start >= meet_anthony_end + 17  # Travel from Financial to Mission takes 17 minutes.
    )
    
    # Scenario 2: Meet Laura first, then Anthony.
    scenario2 = And(
        meet_laura_start >= 7,  # Travel from Castro to Mission takes 7 minutes.
        meet_anthony_start >= meet_laura_end + 17  # Travel from Mission to Financial takes 17 minutes.
    )
    
    # Add either scenario1 or scenario2 to the solver.
    s.add(Or(scenario1, scenario2))
    
    # Check if a solution exists.
    if s.check() == sat:
        m = s.model()
        laura_start = m.eval(meet_laura_start).as_long()
        anthony_start = m.eval(meet_anthony_start).as_long()
        
        # Convert times back to HH:MM format.
        def minutes_to_time(minutes):
            hours = 9 + (minutes // 60)
            mins = minutes % 60
            return f"{hours}:{mins:02d}"
        
        laura_start_time = minutes_to_time(laura_start)
        anthony_start_time = minutes_to_time(anthony_start)
        
        print("SOLUTION:")
        print(f"Meet Anthony at Financial District from {anthony_start_time} for 30 minutes.")
        print(f"Meet Laura at Mission District from {laura_start_time} for 75 minutes.")
    else:
        print("No feasible schedule found.")

solve_scheduling()