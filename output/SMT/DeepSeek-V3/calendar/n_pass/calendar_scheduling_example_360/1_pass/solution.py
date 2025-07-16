from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    solver = Solver()
    
    # Define the start time variable in minutes from 9:00 (0 minutes is 9:00)
    start_time = Int('start_time')
    meeting_duration = 30  # minutes
    
    # Work hours: 9:00 to 17:00 is 8 hours = 480 minutes
    min_time = 0   # 9:00 in minutes from 9:00
    max_time = 480 - meeting_duration  # Latest start time is 16:30
    
    # Constraint: start_time must be within work hours and allow for the meeting duration
    solver.add(start_time >= min_time)
    solver.add(start_time <= max_time)
    
    # Each participant's busy times in minutes from 9:00
    # Emily: 10:00-10:30 (60-90), 16:00-16:30 (420-450)
    emily_busy = [(60, 90), (420, 450)]
    # Mason: free all day
    mason_busy = []
    # Maria: 10:30-11:00 (90-120), 14:00-14:30 (300-330)
    maria_busy = [(90, 120), (300, 330)]
    # Carl: 9:30-10:00 (30-60), 10:30-12:30 (90-210), 13:30-14:00 (270-300), 14:30-15:30 (330-390), 16:00-17:00 (420-480)
    carl_busy = [(30, 60), (90, 210), (270, 300), (330, 390), (420, 480)]
    # David: 9:30-11:00 (30-120), 11:30-12:00 (150-180), 12:30-13:30 (210-270), 14:00-15:00 (300-360), 16:00-17:00 (420-480)
    david_busy = [(30, 120), (150, 180), (210, 270), (300, 360), (420, 480)]
    # Frank: 9:30-10:30 (30-90), 11:00-11:30 (120-150), 12:30-13:30 (210-270), 14:30-17:00 (330-480)
    frank_busy = [(30, 90), (120, 150), (210, 270), (330, 480)]
    
    # Combine all participants' busy times
    all_busy = {
        'Emily': emily_busy,
        'Mason': mason_busy,
        'Maria': maria_busy,
        'Carl': carl_busy,
        'David': david_busy,
        'Frank': frank_busy
    }
    
    # For each participant, add constraints that the meeting does not overlap with their busy times
    for participant, busy_times in all_busy.items():
        for (busy_start, busy_end) in busy_times:
            # The meeting should not overlap with this busy slot
            # So either meeting ends before busy starts or starts after busy ends
            solver.add(Or(
                start_time + meeting_duration <= busy_start,
                start_time >= busy_end
            ))
    
    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model.evaluate(start_time).as_long()
        
        # Convert start_minutes back to HH:MM format
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        start_time_str = f"{start_hour:02d}:{start_minute:02d}"
        
        end_minutes = start_minutes + meeting_duration
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        end_time_str = f"{end_hour:02d}:{end_minute:02d}"
        
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()