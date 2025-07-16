from z3 import *

def solve_meeting_schedule():
    # Define the start time variable (in minutes from 9:00)
    start_time = Int('start_time')
    
    # Work hours: 9:00 to 17:00 (480 minutes from 9:00 to 17:00)
    total_minutes_in_work_hours = 8 * 60  # 9:00-17:00 is 8 hours
    
    # Meeting duration is 30 minutes
    meeting_duration = 30
    end_time = start_time + meeting_duration
    
    # Initialize solver
    solver = Solver()
    
    # Constraint: start_time must be within work hours (0 to 480 - meeting_duration minutes)
    solver.add(start_time >= 0)
    solver.add(end_time <= total_minutes_in_work_hours)
    
    # Each person's busy intervals in minutes from 9:00
    # Jacob's busy intervals: 13:30-14:00 (270-300), 14:30-15:00 (330-360)
    jacob_busy = [(270, 300), (330, 360)]
    # Diana's busy intervals: 9:30-10:00 (30-60), 11:30-12:00 (150-180), 13:00-13:30 (240-270), 16:00-16:30 (420-450)
    diana_busy = [(30, 60), (150, 180), (240, 270), (420, 450)]
    # Adam's busy intervals: 9:30-10:30 (30-90), 11:00-12:30 (120-210), 15:30-16:00 (390-420)
    adam_busy = [(30, 90), (120, 210), (390, 420)]
    # Angela's busy intervals: 9:30-10:00 (30-60), 10:30-12:00 (90-180), 13:00-15:30 (240-390), 16:00-16:30 (420-450)
    angela_busy = [(30, 60), (90, 180), (240, 390), (420, 450)]
    # Dennis's busy intervals: 9:00-9:30 (0-30), 10:30-11:30 (90-150), 13:00-15:00 (240-360), 16:30-17:00 (450-480)
    dennis_busy = [(0, 30), (90, 150), (240, 360), (450, 480)]
    
    # Combine all busy intervals for all participants
    all_busy = []
    all_busy.extend(jacob_busy)
    all_busy.extend(diana_busy)
    all_busy.extend(adam_busy)
    all_busy.extend(angela_busy)
    all_busy.extend(dennis_busy)
    
    # Add constraints that the meeting does not overlap with any busy interval
    for (busy_start, busy_end) in all_busy:
        solver.add(Or(
            end_time <= busy_start,
            start_time >= busy_end
        ))
    
    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model[start_time].as_long()
        
        # Convert start_minutes back to HH:MM format
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        end_minutes = start_minutes + meeting_duration
        end_hours = 9 + end_minutes // 60
        end_minutes_remainder = end_minutes % 60
        end_time_str = f"{end_hours:02d}:{end_minutes_remainder:02d}"
        
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_meeting_schedule()