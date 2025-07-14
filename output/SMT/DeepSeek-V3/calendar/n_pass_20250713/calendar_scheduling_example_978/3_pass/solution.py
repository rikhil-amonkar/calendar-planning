from z3 import *

def solve_scheduling():
    # Create the solver
    s = Optimize()
    
    # Days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
    day = Int('day')
    start_time = Int('start_time')  # in minutes from 9:00 (e.g., 0 = 9:00, 60 = 10:00)
    
    # Meeting duration is 1 hour (60 minutes)
    end_time = start_time + 60
    
    # Work hours are 9:00 to 17:00 (480 minutes from 9:00)
    s.add(day >= 0, day <= 4)
    s.add(start_time >= 0, end_time <= 480)
    
    # Brian's busy times per day (each entry is (start, end) in minutes from 9:00)
    brian_busy = {
        0: [(30, 60), (150, 210), (210, 240), (270, 300)],  # Monday
        1: [(0, 30)],                                       # Tuesday
        2: [(210, 300), (450, 480)],                        # Wednesday
        3: [(120, 150), (240, 270), (450, 480)],           # Thursday
        4: [(30, 60), (90, 120), (240, 270), (360, 420), (450, 480)]  # Friday
    }
    
    # Julia's busy times per day
    julia_busy = {
        0: [(0, 60), (120, 150), (210, 240), (270, 300)],  # Monday
        1: [(240, 300), (420, 450)],                        # Tuesday
        2: [(0, 150), (180, 210), (240, 480)],              # Wednesday
        3: [(0, 90), (120, 480)],                           # Thursday
        4: [(0, 60), (90, 150), (210, 300), (330, 360), (390, 420)]  # Friday
    }
    
    # Function to check if the meeting time overlaps with any busy interval
    def no_overlap(meeting_start, meeting_end, busy_intervals):
        return And([Or(meeting_end <= busy_start, meeting_start >= busy_end) 
                    for (busy_start, busy_end) in busy_intervals])
    
    # Constraints for Brian and Julia's busy times
    for d in range(5):
        s.add(Implies(day == d,
                      And(no_overlap(start_time, end_time, brian_busy[d]),
                          no_overlap(start_time, end_time, julia_busy[d]))))
    
    # Brian prefers to avoid Monday (day 0), so we add a soft constraint
    s.add_soft(day != 0, weight=1)
    
    # Minimize the start time to get the earliest possible meeting
    s.minimize(start_time)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        chosen_day = m[day].as_long()
        start = m[start_time].as_long()
        
        # Convert day index to day name
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_name = days[chosen_day]
        
        # Convert start time from minutes to HH:MM format
        start_hh = 9 + start // 60
        start_mm = start % 60
        start_time_str = f"{start_hh:02d}:{start_mm:02d}"
        
        # Calculate end time (start + 60 minutes)
        end_hh = 9 + (start + 60) // 60
        end_mm = (start + 60) % 60
        end_time_str = f"{end_hh:02d}:{end_mm:02d}"
        
        # Print the solution
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()