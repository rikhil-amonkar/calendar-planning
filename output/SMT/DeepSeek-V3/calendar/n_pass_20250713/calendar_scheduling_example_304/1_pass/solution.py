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
    christine_busy = [(9.5*60 - 9*60, 10.5*60 - 9*60),  # 9:30-10:30 → 30-90
                      (12*60 - 9*60, 12.5*60 - 9*60),    # 12:00-12:30 → 180-210
                      (13*60 - 9*60, 13.5*60 - 9*60),    # 13:00-13:30 → 240-270
                      (14.5*60 - 9*60, 15*60 - 9*60),    # 14:30-15:00 → 330-360
                      (16*60 - 9*60, 16.5*60 - 9*60)]    # 16:00-16:30 → 420-450
    
    # Bobby's busy intervals
    bobby_busy = [(12*60 - 9*60, 12.5*60 - 9*60),       # 12:00-12:30 → 180-210
                  (14.5*60 - 9*60, 15*60 - 9*60)]       # 14:30-15:00 → 330-360
    
    # Elizabeth's busy intervals
    elizabeth_busy = [(9*60 - 9*60, 9.5*60 - 9*60),      # 9:00-9:30 → 0-30
                      (11.5*60 - 9*60, 13*60 - 9*60),    # 11:30-13:00 → 150-240
                      (13.5*60 - 9*60, 14*60 - 9*60),     # 13:30-14:00 → 270-300
                      (15*60 - 9*60, 15.5*60 - 9*60),     # 15:00-15:30 → 360-390
                      (16*60 - 9*60, 17*60 - 9*60)]       # 16:00-17:00 → 420-480
    
    # Tyler's busy intervals
    tyler_busy = [(9*60 - 9*60, 11*60 - 9*60),           # 9:00-11:00 → 0-120
                  (12*60 - 9*60, 12.5*60 - 9*60),        # 12:00-12:30 → 180-210
                  (13*60 - 9*60, 13.5*60 - 9*60),         # 13:00-13:30 → 240-270
                  (15.5*60 - 9*60, 16*60 - 9*60),        # 15:30-16:00 → 390-420
                  (16.5*60 - 9*60, 17*60 - 9*60)]        # 16:30-17:00 → 450-480
    
    # Edward's busy intervals
    edward_busy = [(9*60 - 9*60, 9.5*60 - 9*60),         # 9:00-9:30 → 0-30
                   (10*60 - 9*60, 11*60 - 9*60),         # 10:00-11:00 → 60-120
                   (11.5*60 - 9*60, 14*60 - 9*60),       # 11:30-14:00 → 150-300
                   (14.5*60 - 9*60, 15.5*60 - 9*60),     # 14:30-15:30 → 330-390
                   (16*60 - 9*60, 17*60 - 9*60)]         # 16:00-17:00 → 420-480
    
    # Janice's preference: not after 13:00 (240 minutes from 9:00)
    s.add(Or(start_time + meeting_duration <= 240, start_time >= 240))
    # Wait, no: Janice would rather not meet after 13:00. So the meeting should not start after 13:00 - duration.
    # So start_time + duration <= 240 (13:00) or start_time >= 240.
    # But that's not quite right. Alternatively, the meeting should not overlap with (240, ...).
    # So perhaps the meeting must be entirely before or after 13:00.
    s.add(Or(end_time <= 240, start_time >= 240))
    
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