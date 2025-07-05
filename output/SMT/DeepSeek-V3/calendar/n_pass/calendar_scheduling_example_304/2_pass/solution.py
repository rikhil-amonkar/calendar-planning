from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the start time in minutes from 9:00 (0 is 9:00, 480 is 17:00)
    start_time = Int('start_time')
    meeting_duration = 30
    end_time = start_time + meeting_duration
    
    # Constraint: Meeting must be within work hours (9:00-17:00)
    s.add(start_time >= 0)
    s.add(end_time <= 480)  # 17:00 is 8 hours after 9:00 (8*60=480)
    
    # Define each person's busy intervals in minutes from 9:00
    # Christine's busy intervals
    christine_busy = [(30, 90),     # 9:30-10:30
                      (180, 210),    # 12:00-12:30
                      (240, 270),    # 13:00-13:30
                      (330, 360),    # 14:30-15:00
                      (420, 450)]    # 16:00-16:30
    
    # Bobby's busy intervals
    bobby_busy = [(180, 210),       # 12:00-12:30
                  (330, 360)]       # 14:30-15:00
    
    # Elizabeth's busy intervals
    elizabeth_busy = [(0, 30),      # 9:00-9:30
                      (150, 240),    # 11:30-13:00
                      (270, 300),    # 13:30-14:00
                      (360, 390),    # 15:00-15:30
                      (420, 480)]    # 16:00-17:00
    
    # Tyler's busy intervals
    tyler_busy = [(0, 120),         # 9:00-11:00
                  (180, 210),       # 12:00-12:30
                  (240, 270),       # 13:00-13:30
                  (390, 420),       # 15:30-16:00
                  (450, 480)]       # 16:30-17:00
    
    # Edward's busy intervals
    edward_busy = [(0, 30),         # 9:00-9:30
                   (60, 120),       # 10:00-11:00
                   (150, 300),      # 11:30-14:00
                   (330, 390),      # 14:30-15:30
                   (420, 480)]      # 16:00-17:00
    
    # Janice's preference: not after 13:00 (240 minutes from 9:00)
    s.add(end_time <= 240)
    
    # Function to add constraints for avoiding busy intervals
    def add_busy_constraints(busy_intervals):
        for (busy_start, busy_end) in busy_intervals:
            s.add(Or(end_time <= busy_start, start_time >= busy_end))
    
    # Add constraints for each person's busy intervals
    add_busy_constraints(christine_busy)
    add_busy_constraints(bobby_busy)
    add_busy_constraints(elizabeth_busy)
    add_busy_constraints(tyler_busy)
    add_busy_constraints(edward_busy)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start = m[start_time].as_long()
        
        # Convert start time back to HH:MM
        total_minutes = start
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_str = f"{hours:02d}:{minutes:02d}"
        
        end_total = start + 30
        end_hours = 9 + end_total // 60
        end_minutes = end_total % 60
        end_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found.")

solve_scheduling()