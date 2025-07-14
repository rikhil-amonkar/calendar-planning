from z3 import *

def solve_scheduling_problem():
    # Initialize the solver
    solver = Solver()
    
    # Define the start time variable in minutes from 9:00 (0 minutes)
    start_time = Int('start_time')
    
    # Meeting duration is 30 minutes
    duration = 30
    end_time = start_time + duration
    
    # Total working hours: 9:00 (0) to 17:00 (480 minutes)
    solver.add(start_time >= 0)
    solver.add(end_time <= 480)
    
    # Lisa's busy slots in minutes from 9:00
    lisa_busy = [
        (0, 60),    # 9:00-10:00
        (90, 150),   # 10:30-11:30
        (210, 240),  # 12:30-13:00
        (420, 450)    # 16:00-16:30
    ]
    
    # Bobby's busy slots
    bobby_busy = [
        (0, 30),     # 9:00-9:30
        (60, 90),     # 10:00-10:30
        (150, 180),   # 11:30-12:00
        (360, 390)    # 15:00-15:30
    ]
    
    # Bobby's preference: meeting should end by 15:00 (360 minutes)
    solver.add(end_time <= 360)
    
    # Randy's busy slots
    randy_busy = [
        (30, 60),     # 9:30-10:00
        (90, 120),     # 10:30-11:00
        (150, 210),    # 11:30-12:30
        (240, 270),    # 13:00-13:30
        (330, 390),    # 14:30-15:30
        (420, 450)     # 16:00-16:30
    ]
    
    # Function to add no-overlap constraints
    def add_no_overlap(busy_slots):
        for (busy_start, busy_end) in busy_slots:
            solver.add(Or(
                end_time <= busy_start,
                start_time >= busy_end
            ))
    
    # Add constraints for each participant
    add_no_overlap(lisa_busy)
    add_no_overlap(bobby_busy)
    add_no_overlap(randy_busy)
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_min = model.evaluate(start_time).as_long()
        
        # Convert start_min back to HH:MM
        hours = 9 + (start_min // 60)
        minutes = start_min % 60
        start_str = f"{hours:02d}:{minutes:02d}"
        
        end_min = start_min + duration
        end_hours = 9 + (end_min // 60)
        end_minutes = end_min % 60
        end_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

solve_scheduling_problem()