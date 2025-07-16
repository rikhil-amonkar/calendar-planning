from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()
    
    # All times in minutes since 9:00 AM (time 0)
    # Convert availability window:
    # 8:45 PM is 11h45m after 9:00 AM = 705 minutes
    # 9:30 PM is 12h30m after 9:00 AM = 750 minutes
    
    # Decision variables (all in minutes since 9:00 AM)
    departure = Int('departure')       # When we leave Alamo Square
    arrival = Int('arrival')           # When we arrive at Richmond
    meeting_end = Int('meeting_end')   # When we leave Richmond
    
    # Travel times (minutes)
    to_richmond = 12
    from_richmond = 13
    
    # Add constraints
    # 1. We can't leave before 9:00 AM (time 0)
    s.add(departure >= 0)
    
    # 2. Travel time to Richmond is 12 minutes
    s.add(arrival == departure + to_richmond)
    
    # 3. Must meet for at least 45 minutes
    s.add(meeting_end >= arrival + 45)
    
    # 4. Must arrive during Timothy's window (705-750)
    s.add(arrival >= 705)
    s.add(meeting_end <= 750)
    
    # 5. Additional constraints to prevent negative times
    s.add(arrival >= 0)
    s.add(meeting_end >= 0)
    
    # Find solution
    if s.check() == sat:
        m = s.model()
        
        # Helper function to format times
        def format_time(mins):
            # Convert minutes since 9:00 AM to clock time
            total_mins = 540 + mins  # 9:00 AM = 540 mins since midnight
            hours = (total_mins // 60) % 24
            minutes = total_mins % 60
            period = "AM" if hours < 12 else "PM"
            display_hour = hours if hours <= 12 else hours - 12
            if display_hour == 0:
                display_hour = 12
            return f"{display_hour}:{minutes:02d} {period}"
        
        # Get solution values
        depart_time = m[departure].as_long()
        arrive_time = m[arrival].as_long()
        end_time = m[meeting_end].as_long()
        
        print("Optimal Schedule:")
        print(f"Depart Alamo Square at: {format_time(depart_time)}")
        print(f"Arrive Richmond District at: {format_time(arrive_time)}")
        print(f"Meet Timothy until: {format_time(end_time)}")
        print(f"Meeting Duration: {end_time - arrive_time} minutes")
    else:
        print("No valid schedule found")

solve_scheduling()