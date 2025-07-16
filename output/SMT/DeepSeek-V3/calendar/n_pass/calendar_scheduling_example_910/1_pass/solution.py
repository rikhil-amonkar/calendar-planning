from z3 import *

def solve_meeting_schedule():
    # Initialize the solver
    solver = Solver()
    
    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
    start_time = Int('start_time')  # in minutes from 9:00 (e.g., 0 is 9:00, 60 is 10:00)
    end_time = Int('end_time')
    
    # Day constraints: day must be 0-4 (Monday to Friday)
    solver.add(day >= 0, day <= 4)
    
    # Bryan prefers to avoid Tuesday (day 1)
    solver.add(day != 1)
    
    # Nicholas prefers to avoid Monday (day 0) and Thursday (day 3)
    solver.add(day != 0, day != 3)
    
    # Now possible days are 2 (Wednesday) or 4 (Friday)
    
    # Meeting duration is 1 hour (60 minutes)
    solver.add(end_time == start_time + 60)
    
    # Work hours are 9:00 to 17:00 (480 minutes from 9:00)
    solver.add(start_time >= 0, end_time <= 480)  # 8 hours * 60 minutes = 480
    
    # Function to add busy slots for a person on a specific day
    def add_busy_slots(day_val, busy_slots):
        # busy_slots is a list of (start, end) in minutes from 9:00
        for (busy_start, busy_end) in busy_slots:
            solver.add(Not(And(day == day_val,
                               start_time < busy_end,
                               end_time > busy_start)))
    
    # Bryan's busy slots per day
    bryan_busy = {
        3: [(30, 60), (150, 180)],  # Thursday: 9:30-10:00, 12:30-13:00
        4: [(90, 120), (300, 330)]   # Friday: 10:30-11:00, 14:00-14:30
    }
    
    # Nicholas's busy slots per day
    nicholas_busy = {
        0: [(150, 180), (240, 390)],  # Monday: 11:30-12:00, 13:00-15:30
        1: [(0, 30), (120, 270), (300, 450)],  # Tuesday: 9:00-9:30, 11:00-13:30, 14:00-16:30
        2: [(0, 30), (60, 120), (150, 270), (300, 330), (360, 450)],  # Wednesday: 9:00-9:30, 10:00-11:00, 11:30-13:30, 14:00-14:30, 15:00-16:30
        3: [(90, 150), (180, 210), (360, 390), (450, 480)],  # Thursday: 10:30-11:30, 12:00-12:30, 15:00-15:30, 16:30-17:00
        4: [(0, 90), (120, 180), (210, 330), (390, 420), (450, 480)]  # Friday: 9:00-10:30, 11:00-12:00, 12:30-14:30, 15:30-16:00, 16:30-17:00
    }
    
    # Add constraints for Bryan's busy slots
    for d in bryan_busy:
        add_busy_slots(d, bryan_busy[d])
    
    # Add constraints for Nicholas's busy slots
    for d in nicholas_busy:
        add_busy_slots(d, nicholas_busy[d])
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        day_val = model[day].as_long()
        start_val = model[start_time].as_long()
        end_val = model[end_time].as_long()
        
        # Convert day_val to day name
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_name = days[day_val]
        
        # Convert start and end times to HH:MM format
        start_hh = 9 + start_val // 60
        start_mm = start_val % 60
        end_hh = 9 + end_val // 60
        end_mm = end_val % 60
        
        # Format as two-digit strings
        start_time_str = f"{start_hh:02d}:{start_mm:02d}"
        end_time_str = f"{end_hh:02d}:{end_mm:02d}"
        
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_meeting_schedule()