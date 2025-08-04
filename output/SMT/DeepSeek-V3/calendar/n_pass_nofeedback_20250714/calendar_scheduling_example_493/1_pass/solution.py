from z3 import *

def solve_meeting_schedule():
    # Initialize the solver
    s = Solver()
    
    # Define the start time as an integer (minutes from 9:00)
    start_time = Int('start_time')
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Total working hours from 9:00 to 17:00 is 8 hours = 480 minutes
    # So start_time must be between 0 and 450 (since 450 + 30 = 480)
    s.add(start_time >= 0)
    s.add(start_time <= 450)
    
    # Define each person's busy slots in minutes from 9:00
    # Each slot is a tuple (start, end)
    
    # Stephanie's busy slots: 11:00-11:30 (120-150), 14:30-15:00 (330-360)
    stephanie_busy = [(120, 150), (330, 360)]
    
    # Joe's busy slots: 9:00-9:30 (0-30), 10:00-12:00 (60-180), 12:30-13:00 (210-240), 14:00-17:00 (300-480)
    joe_busy = [(0, 30), (60, 180), (210, 240), (300, 480)]
    
    # Diana's busy slots: 9:00-10:30 (0-90), 11:30-12:00 (150-180), 13:00-14:00 (240-300), 14:30-15:30 (330-390), 16:00-17:00 (420-480)
    diana_busy = [(0, 90), (150, 180), (240, 300), (330, 390), (420, 480)]
    
    # Deborah's busy slots: 9:00-10:00 (0-60), 10:30-12:00 (90-180), 12:30-13:00 (210-240), 13:30-14:00 (270-300), 14:30-15:30 (330-390), 16:00-16:30 (420-450)
    deborah_busy = [(0, 60), (90, 180), (210, 240), (270, 300), (330, 390), (420, 450)]
    
    # For each person, add constraints that the meeting does not overlap with any of their busy slots
    # The meeting is from start_time to start_time + duration
    # For a busy slot (busy_start, busy_end), the meeting must either:
    #   end before busy_start OR start after busy_end
    
    # Stephanie's constraints
    for (busy_start, busy_end) in stephanie_busy:
        s.add(Or(start_time + duration <= busy_start, start_time >= busy_end))
    
    # Joe's constraints
    for (busy_start, busy_end) in joe_busy:
        s.add(Or(start_time + duration <= busy_start, start_time >= busy_end))
    
    # Diana's constraints
    for (busy_start, busy_end) in diana_busy:
        s.add(Or(start_time + duration <= busy_start, start_time >= busy_end))
    
    # Deborah's constraints
    for (busy_start, busy_end) in deborah_busy:
        s.add(Or(start_time + duration <= busy_start, start_time >= busy_end))
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_minutes = m[start_time].as_long()
        
        # Convert start_minutes back to HH:MM format
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + duration
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
        print(f"End Time: {end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

solve_meeting_schedule()