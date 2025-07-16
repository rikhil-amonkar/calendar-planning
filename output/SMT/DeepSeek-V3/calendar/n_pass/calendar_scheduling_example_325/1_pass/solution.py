from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    solver = Solver()
    
    # Work hours are 9:00 to 17:00 (480 minutes)
    work_start = 0  # 9:00 in minutes since 9:00
    work_end = 480   # 17:00 in minutes since 9:00
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Define the start time variable (in minutes since 9:00)
    start_time = Int('start_time')
    
    # Constraint: start_time must be within work hours and leave room for duration
    solver.add(start_time >= work_start)
    solver.add(start_time + duration <= work_end)
    
    # Jose's constraint: not after 15:30 (which is 390 minutes from 9:00)
    # So start_time + duration <= 390
    solver.add(start_time + duration <= 390)
    
    # Define each participant's busy slots in minutes since 9:00
    # Each slot is (start, end)
    jose_busy = [(120, 150), (210, 240)]  # 11:00-11:30, 12:30-13:00
    keith_busy = [(300, 330), (360, 390)]  # 14:00-14:30, 15:00-15:30
    logan_busy = [(0, 60), (180, 210), (360, 390)]  # 9:00-10:00, 12:00-12:30, 15:00-15:30
    megan_busy = [(0, 90), (120, 180), (240, 270), (330, 450)]  # 9:00-10:30, 11:00-12:00, 13:00-13:30, 14:30-16:30
    gary_busy = [(0, 30), (60, 90), (150, 240), (270, 300), (330, 450)]  # 9:00-9:30, 10:00-10:30, 11:30-13:00, 13:30-14:00, 14:30-16:30
    bobby_busy = [(120, 150), (180, 210), (240, 420)]  # 11:00-11:30, 12:00-12:30, 13:00-16:00
    
    # Function to add constraints that the meeting does not overlap with any busy slot
    def add_no_overlap_constraints(busy_slots):
        for (busy_start, busy_end) in busy_slots:
            # The meeting is either entirely before the busy slot or entirely after
            solver.add(Or(
                start_time + duration <= busy_start,
                start_time >= busy_end
            ))
    
    # Add constraints for each participant
    add_no_overlap_constraints(jose_busy)
    add_no_overlap_constraints(keith_busy)
    add_no_overlap_constraints(logan_busy)
    add_no_overlap_constraints(megan_busy)
    add_no_overlap_constraints(gary_busy)
    add_no_overlap_constraints(bobby_busy)
    
    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model.evaluate(start_time).as_long()
        
        # Convert start_minutes back to HH:MM format
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        end_minutes = start_minutes + duration
        end_hours = 9 + end_minutes // 60
        end_minutes_remainder = end_minutes % 60
        end_time_str = f"{end_hours:02d}:{end_minutes_remainder:02d}"
        
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()