from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the possible days (Monday=0, Tuesday=1, Wednesday=2, Thursday=3)
    day = Int('day')
    s.add(day >= 0, day <= 3)
    
    # Define the start time in minutes from 9:00 (0 minutes = 9:00)
    start_time = Int('start_time')
    # Meeting duration is 1 hour (60 minutes)
    duration = 60
    # Work hours are 9:00 to 17:00 (8 hours = 480 minutes)
    s.add(start_time >= 0, start_time + duration <= 480)
    
    # Carl's busy slots per day (each slot is (start, end) in minutes from 9:00)
    carl_busy = {
        0: [(120, 150)],  # Monday 11:00-11:30 (120-150)
        1: [(330, 360)],  # Tuesday 14:30-15:00 (330-360)
        2: [(60, 150), (240, 270)],  # Wednesday 10:00-11:30 (60-150), 13:00-13:30 (240-270)
        3: [(270, 300), (420, 450)]   # Thursday 13:30-14:00 (270-300), 16:00-16:30 (420-450)
    }
    
    # Margaret's busy slots per day
    margaret_busy = {
        0: [(0, 90), (120, 480)],  # Monday 9:00-10:30 (0-90), 11:00-17:00 (120-480)
        1: [(30, 180), (270, 300), (390, 480)],  # Tuesday 9:30-12:00 (30-180), 13:30-14:00 (270-300), 15:30-17:00 (390-480)
        2: [(30, 180), (210, 240), (270, 330), (360, 480)],  # Wednesday 9:30-12:00 (30-180), 12:30-13:00 (210-240), 13:30-14:30 (270-330), 15:00-17:00 (360-480)
        3: [(60, 180), (210, 300), (330, 480)]  # Thursday 10:00-12:00 (60-180), 12:30-14:00 (210-300), 14:30-17:00 (330-480)
    }
    
    # Function to check if the meeting overlaps with any busy slot
    def no_overlap(day_val, start, end, busy_slots):
        return And([Or(day != day_val, end <= slot_start, start >= slot_end) 
                    for slot_start, slot_end in busy_slots])
    
    # Add constraints for Carl and Margaret
    for d in range(4):
        # Carl's constraints
        s.add(Implies(day == d, no_overlap(d, start_time, start_time + duration, carl_busy[d])))
        # Margaret's constraints
        s.add(Implies(day == d, no_overlap(d, start_time, start_time + duration, margaret_busy[d])))
    
    # Carl prefers to avoid Thursday (day=3), so we prioritize other days
    # We first check if there's a solution not on Thursday
    temp_solver = Solver()
    temp_solver.add(s.assertions())
    temp_solver.add(day != 3)
    if temp_solver.check() == sat:
        m = temp_solver.model()
    else:
        # If no solution on other days, check Thursday
        s.check()
        m = s.model()
    
    # Extract the solution
    day_val = m[day].as_long()
    start_val = m[start_time].as_long()
    
    # Convert day_val to day name
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    day_name = days[day_val]
    
    # Convert start time from minutes to HH:MM format
    start_hour = 9 + start_val // 60
    start_min = start_val % 60
    start_time_str = f"{start_hour:02d}:{start_min:02d}"
    
    # Calculate end time
    end_hour = 9 + (start_val + duration) // 60
    end_min = (start_val + duration) % 60
    end_time_str = f"{end_hour:02d}:{end_min:02d}"
    
    print(f"SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")

solve_scheduling()