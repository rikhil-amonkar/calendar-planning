from z3 import *

def main():
    # Define variables
    day = Int('day')
    start = Int('start')
    
    # Participants' busy times (in minutes from 00:00)
    stephanie_busy = {
        0: [(570, 600), (630, 660), (690, 720), (840, 870)],
        1: [(720, 780)],
        2: [(540, 600), (780, 840)]
    }
    
    betty_busy = {
        0: [(540, 600), (660, 690), (870, 900), (930, 960)],
        1: [(540, 570), (690, 720), (750, 870), (930, 960)],
        2: [(600, 690), (720, 840), (870, 1020)]
    }
    
    # Initialize solver
    s = Solver()
    
    # Day must be 0 (Mon), 1 (Tue), or 2 (Wed)
    s.add(day >= 0, day <= 2)
    # Start time must be within work hours (9:00 to 16:00 inclusive for 1-hour meeting)
    s.add(start >= 540, start <= 960)
    
    # Function to add non-overlap constraints
    def add_non_overlap(busy_intervals, d):
        for s_busy, e_busy in busy_intervals.get(d, []):
            s.add(If(day == d, (start + 60 <= s_busy) Or (start >= e_busy), True))
    
    # Add constraints for Stephanie
    for d in stephanie_busy:
        add_non_overlap(stephanie_busy, d)
    
    # Add constraints for Betty
    for d in betty_busy:
        add_non_overlap(betty_busy, d)
    
    # Betty cannot meet on Tuesday after 12:30 (750 minutes)
    s.add(If(day == 1, start + 60 <= 750, True))
    
    # Try to avoid Monday first
    s.push()
    s.add(day != 0)
    
    if s.check() == sat:
        m = s.model()
        proposed_day = m[day].as_long()
        proposed_start = m[start].as_long()
    else:
        s.pop()
        if s.check() == sat:
            m = s.model()
            proposed_day = m[day].as_long()
            proposed_start = m[start].as_long()
        else:
            print("No solution found")
            return
    
    # Convert to readable format
    day_names = ['Monday', 'Tuesday', 'Wednesday']
    day_name = day_names[proposed_day]
    
    start_hour = proposed_start // 60
    start_minute = proposed_start % 60
    end_time = proposed_start + 60
    end_hour = end_time // 60
    end_minute = end_time % 60
    
    time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
    
    print(day_name)
    print(time_str)

if __name__ == "__main__":
    main()