from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()
    
    # Meeting start and end times (in minutes since 9:00 AM)
    meet_laura_start = Int('meet_laura_start')
    meet_laura_end = Int('meet_laura_end')
    meet_anthony_start = Int('meet_anthony_start')
    meet_anthony_end = Int('meet_anthony_end')
    
    # Availability windows (minutes since 9:00 AM)
    # Laura: 12:15 PM (195 min) to 7:45 PM (645 min)
    # Anthony: 12:30 PM (210 min) to 2:45 PM (345 min)
    laura_min, laura_max = 195, 645
    anthony_min, anthony_max = 210, 345
    
    # Meeting duration constraints
    s.add(meet_laura_end == meet_laura_start + 75)
    s.add(meet_anthony_end == meet_anthony_start + 30)
    
    # Availability constraints
    s.add(meet_laura_start >= laura_min)
    s.add(meet_laura_end <= laura_max)
    s.add(meet_anthony_start >= anthony_min)
    s.add(meet_anthony_end <= anthony_max)
    
    # Travel times (minutes)
    castro_to_mission = 7
    castro_to_financial = 20
    mission_to_financial = 17
    financial_to_mission = 17
    
    # Scenario 1: Meet Anthony first, then Laura
    scenario1 = And(
        meet_anthony_start >= castro_to_financial,
        meet_laura_start >= meet_anthony_end + financial_to_mission
    )
    
    # Scenario 2: Meet Laura first, then Anthony
    scenario2 = And(
        meet_laura_start >= castro_to_mission,
        meet_anthony_start >= meet_laura_end + mission_to_financial
    )
    
    # Add either scenario to the solver
    s.add(Or(scenario1, scenario2))
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        laura_start = m.eval(meet_laura_start).as_long()
        anthony_start = m.eval(meet_anthony_start).as_long()
        
        # Convert minutes to HH:MM format
        def format_time(minutes):
            hours = 9 + minutes // 60
            minutes = minutes % 60
            return f"{hours}:{minutes:02d}"
        
        print("SOLUTION:")
        print(f"Meet Anthony at Financial District from {format_time(anthony_start)} for 30 minutes")
        print(f"Meet Laura at Mission District from {format_time(laura_start)} for 75 minutes")
    else:
        print("No feasible schedule found")

solve_scheduling()