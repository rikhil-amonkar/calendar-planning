from z3 import *

def solve_scheduling():
    # Initialize the solver
    solver = Solver()
    
    # Define the start time in minutes from 9:00 (0 minutes is 9:00)
    start_time = Int('start_time')
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Total available minutes from 9:00 to 17:00 is 8 hours = 480 minutes
    max_time = 480
    
    # Constraint: start_time must be >= 0 and <= (max_time - duration)
    solver.add(start_time >= 0)
    solver.add(start_time <= max_time - duration)
    
    # Define each person's blocked time slots in minutes from 9:00
    # Each slot is (start, end) in minutes
    joe_slots = [(30, 60), (90, 120)]  # 9:30-10:00, 10:30-11:00
    keith_slots = [(150, 180), (360, 390)]  # 11:30-12:00, 15:00-15:30
    patricia_slots = [(0, 30), (240, 270)]  # 9:00-9:30, 13:00-13:30
    nancy_slots = [(0, 120), (150, 450)]  # 9:00-11:00, 11:30-16:30
    pamela_slots = [(0, 60), (90, 120), (150, 180), (240, 300), (330, 360), (390, 420), (450, 480)]  
    # 9:00-10:00, 10:30-11:00, 11:30-12:30, 13:00-14:00, 14:30-15:00, 15:30-16:00, 16:30-17:00
    
    # Combine all blocked slots
    all_blocked_slots = joe_slots + keith_slots + patricia_slots + nancy_slots + pamela_slots
    
    # For each blocked slot, add constraint that the meeting does not overlap
    for (block_start, block_end) in all_blocked_slots:
        # The meeting is either entirely before the block or entirely after
        solver.add(Or(
            start_time + duration <= block_start,
            start_time >= block_end
        ))
    
    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        start_min = model[start_time].as_long()
        
        # Convert start_min back to HH:MM
        hours = 9 + start_min // 60
        minutes = start_min % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        end_min = start_min + duration
        end_hours = 9 + end_min // 60
        end_minutes = end_min % 60
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()