from z3 import *

def solve_scheduling():
    # Define the days to consider
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    
    # Define work hours (9:00 to 17:00) in minutes since 9:00
    work_start = 0  # 9:00 is 0 minutes
    work_end = 480   # 17:00 is 480 minutes (8 hours later)
    meeting_duration = 60  # 1 hour
    
    # Define the busy slots for Natalie and William for each day in minutes since 9:00
    # Each entry is a list of (start, end) tuples in minutes
    natalie_busy = {
        "Monday": [(0, 30), (60, 180), (150, 180), (300, 330), (360, 450)],
        "Tuesday": [(0, 30), (60, 90), (210, 300), (420, 480)],
        "Wednesday": [(120, 150), (420, 450)],
        "Thursday": [(60, 120), (150, 360), (390, 420), (450, 480)]
    }
    
    william_busy = {
        "Monday": [(30, 120), (150, 480)],
        "Tuesday": [(0, 240), (270, 420)],
        "Wednesday": [(0, 210), (240, 330), (390, 420), (450, 480)],
        "Thursday": [(0, 90), (120, 150), (180, 210), (240, 300), (360, 480)]
    }
    
    # Iterate through each day to find a feasible meeting time
    for day in days:
        s = Solver()
        start_time = Int('start_time')
        
        # Constraint: start_time must be within work hours and leave room for the meeting
        s.add(start_time >= work_start)
        s.add(start_time + meeting_duration <= work_end)
        
        # For each busy slot in Natalie's schedule for the day, add constraint that the meeting does not overlap
        for (busy_start, busy_end) in natalie_busy[day]:
            s.add(Or(start_time >= busy_end, start_time + meeting_duration <= busy_start))
        
        # For each busy slot in William's schedule for the day, add constraint that the meeting does not overlap
        for (busy_start, busy_end) in william_busy[day]:
            s.add(Or(start_time >= busy_end, start_time + meeting_duration <= busy_start))
        
        # Check if there's a solution for this day
        if s.check() == sat:
            model = s.model()
            start_minutes = model[start_time].as_long()
            
            # Convert start_minutes back to HH:MM format
            start_hour = 9 + start_minutes // 60
            start_minute = start_minutes % 60
            end_minutes = start_minutes + meeting_duration
            end_hour = 9 + end_minutes // 60
            end_minute = end_minutes % 60
            
            # Format the time strings with leading zeros
            start_time_str = f"{start_hour:02d}:{start_minute:02d}"
            end_time_str = f"{end_hour:02d}:{end_minute:02d}"
            
            # Print the solution
            print("SOLUTION:")
            print(f"Day: {day}")
            print(f"Start Time: {start_time_str}")
            print(f"End Time: {end_time_str}")
            return
    
    # If no solution found (though the problem states there is one)
    print("No solution found within the given constraints.")

solve_scheduling()