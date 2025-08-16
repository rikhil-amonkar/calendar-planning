from z3 import *

def schedule_meeting():
    solver = Solver()
    start = Int('start')
    
    # Define time boundaries (9:00 AM to 5:00 PM in minutes since midnight)
    solver.add(start >= 540)  # 9:00 AM
    solver.add(start <= 960)  # 4:00 PM (meeting ends at 5:00 PM)
    
    # Collect all blocked intervals from participants
    blocked_intervals = [
        # Olivia's blocked intervals
        (750, 810),  # 12:30 PM - 1:30 PM
        (870, 900),  # 2:30 PM - 3:00 PM
        (990, 1020), # 4:30 PM - 5:00 PM
        # Virginia's blocked intervals
        (540, 600),  # 9:00 AM - 10:00 AM
        (690, 960),  # 11:30 AM - 4:00 PM
        (990, 1020), # 4:30 PM - 5:00 PM
        # Paul's blocked intervals
        (540, 570),  # 9:00 AM - 9:30 AM
        (660, 690),  # 11:00 AM - 11:30 AM
        (780, 840),  # 1:00 PM - 2:00 PM
        (870, 960),  # 2:30 PM - 4:00 PM
        (990, 1020), # 4:30 PM - 5:00 PM
    ]
    
    # Add constraints to avoid overlaps with blocked intervals
    for b_start, b_end in blocked_intervals:
        solver.add(Or(start + 60 <= b_start, start >= b_end))
    
    if solver.check() == sat:
        model = solver.model()
        start_val = model[start].as_long()
        # Convert minutes to HH:MM format
        start_hours = start_val // 60
        start_minutes = start_val % 60
        end_hours = (start_val + 60) // 60
        end_minutes = (start_val + 60) % 60
        start_time = f"{start_hours:02d}:{start_minutes:02d}"
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        return f"SOLUTION:\nDay: Monday\nStart Time: {start_time}\nEnd Time: {end_time}"
    else:
        return "No solution found."

# Example usage:
print(schedule_meeting())