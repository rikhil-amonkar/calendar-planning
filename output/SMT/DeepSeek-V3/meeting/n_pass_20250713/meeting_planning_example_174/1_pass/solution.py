from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables
    # Time spent with Kenneth (Mission District)
    meet_kenneth_start = Int('meet_kenneth_start')  # in minutes from 9:00AM
    meet_kenneth_end = Int('meet_kenneth_end')
    
    # Time spent with Thomas (Pacific Heights)
    meet_thomas_start = Int('meet_thomas_start')    # in minutes from 9:00AM
    meet_thomas_end = Int('meet_thomas_end')
    
    # Travel times (already given, but we need to model the transitions)
    # Nob Hill to Mission District: 13 minutes
    # Mission District to Pacific Heights: 16 minutes
    # Nob Hill to Pacific Heights: 8 minutes
    # etc.

    # Convert friend availability windows to minutes from 9:00AM
    # Kenneth is available from 12:00PM to 3:45PM (180 to 405 minutes from 9:00AM)
    kenneth_start_avail = 180  # 12:00PM is 3 hours after 9:00AM
    kenneth_end_avail = 405     # 3:45PM is 6 hours and 45 minutes after 9:00AM
    
    # Thomas is available from 3:30PM to 7:15PM (390 to 615 minutes from 9:00AM)
    thomas_start_avail = 390    # 3:30PM is 6 hours and 30 minutes after 9:00AM
    thomas_end_avail = 615      # 7:15PM is 10 hours and 15 minutes after 9:00AM
    
    # Meeting duration constraints
    s.add(meet_kenneth_end - meet_kenneth_start >= 45)  # At least 45 minutes with Kenneth
    s.add(meet_thomas_end - meet_thomas_start >= 75)    # At least 75 minutes with Thomas
    
    # Meeting must be within friend's availability
    s.add(meet_kenneth_start >= kenneth_start_avail)
    s.add(meet_kenneth_end <= kenneth_end_avail)
    s.add(meet_thomas_start >= thomas_start_avail)
    s.add(meet_thomas_end <= thomas_end_avail)
    
    # Initial location: Nob Hill at time 0 (9:00AM)
    
    # Possible schedules:
    # Option 1: Nob Hill -> Mission District (meet Kenneth) -> Pacific Heights (meet Thomas)
    # Option 2: Nob Hill -> Pacific Heights (meet Thomas) -> Mission District (meet Kenneth)
    # Option 2 is impossible because Thomas's availability is after Kenneth's.
    # So only Option 1 is feasible.
    
    # Travel from Nob Hill to Mission District takes 13 minutes
    s.add(meet_kenneth_start >= 0 + 13)
    
    # Travel from Mission District to Pacific Heights takes 16 minutes
    s.add(meet_thomas_start >= meet_kenneth_end + 16)
    
    # Check if the schedule is feasible
    if s.check() == sat:
        m = s.model()
        # Convert times back to hours and minutes
        def minutes_to_time(minutes):
            total_minutes = minutes
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{9 + hours}:{mins:02d}"
        
        k_start = m.eval(meet_kenneth_start).as_long()
        k_end = m.eval(meet_kenneth_end).as_long()
        t_start = m.eval(meet_thomas_start).as_long()
        t_end = m.eval(meet_thomas_end).as_long()
        
        print("SOLUTION:")
        print(f"Meet Kenneth at Mission District from {minutes_to_time(k_start)} to {minutes_to_time(k_end)}")
        print(f"Then travel to Pacific Heights and meet Thomas from {minutes_to_time(t_start)} to {minutes_to_time(t_end)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()