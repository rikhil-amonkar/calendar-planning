from z3 import *

def solve_scheduling_problem():
    # Initialize solver
    solver = Solver()
    
    # Variables
    meet_start = Int('meet_start')  # minutes since 9:00 AM
    meet_end = Int('meet_end')      # minutes since 9:00 AM
    travel_to_chinatown = Int('travel_to_chinatown')  # time leaving Golden Gate Park
    
    # David's availability: 4:00 PM (420) to 9:45 PM (645)
    david_start = 420
    david_end = 645
    
    # Travel time to Chinatown is 23 minutes
    travel_time = 23
    
    # Constraints
    # 1. Meeting must be within David's availability
    solver.add(meet_start >= david_start)
    solver.add(meet_end <= david_end)
    
    # 2. Meeting duration must be at least 105 minutes
    solver.add(meet_end - meet_start >= 105)
    
    # 3. You must arrive at Chinatown by meet_start, so leave Golden Gate Park early enough
    solver.add(travel_to_chinatown + travel_time <= meet_start)
    
    # 4. You arrive at Golden Gate Park at 9:00 AM (0 minutes), so travel_to_chinatown >= 0
    solver.add(travel_to_chinatown >= 0)
    
    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()
        m_start = model[meet_start].as_long()
        m_end = model[meet_end].as_long()
        travel_time_leaving = model[travel_to_chinatown].as_long()
        
        # Convert minutes to time format
        def minutes_to_time(m):
            hours = 9 + m // 60
            minutes = m % 60
            return f"{hours}:{minutes:02d}"
        
        print("SOLUTION:")
        print(f"Leave Golden Gate Park at: {minutes_to_time(travel_time_leaving)}")
        print(f"Meet David from: {minutes_to_time(m_start)} to {minutes_to_time(m_end)}")
        print(f"Meeting duration: {m_end - m_start} minutes")
    else:
        print("No valid schedule found.")

solve_scheduling_problem()