from constraint import Problem

def main():
    # Create a problem instance
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Convert schedules to minutes from midnight
    # Michael's busy times
    michael_busy = [
        (9*60 + 30, 10*60 + 30),   # 9:30-10:30
        (15*60, 15*60 + 30),       # 15:00-15:30
        (16*60, 16*60 + 30)        # 16:00-16:30
    ]
    
    # Eric has no meetings
    eric_busy = []
    
    # Arthur's busy times
    arthur_busy = [
        (9*60, 12*60),             # 9:00-12:00
        (13*60, 15*60),            # 13:00-15:00
        (15*60 + 30, 16*60),       # 15:30-16:00
        (16*60 + 30, 17*60)        # 16:30-17:00
    ]
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_start_times = []
    for minute in range(work_start, work_end - meeting_duration + 1, 15):
        possible_start_times.append(minute)
    
    # Add variable for meeting start time
    problem.addVariable('start_time', possible_start_times)
    
    # Define constraint function
    def is_time_available(start_time):
        end_time = start_time + meeting_duration
        
        # Check if time conflicts with Michael's schedule
        for busy_start, busy_end in michael_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check if time conflicts with Arthur's schedule
        for busy_start, busy_end in arthur_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Eric has no conflicts
        return True
    
    # Add constraint
    problem.addConstraint(is_time_available, ['start_time'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if solutions:
        # Get the first solution
        start_time_minutes = solutions[0]['start_time']
        end_time_minutes = start_time_minutes + meeting_duration
        
        # Convert back to HH:MM format
        start_hour = start_time_minutes // 60
        start_minute = start_time_minutes % 60
        end_hour = end_time_minutes // 60
        end_minute = end_time_minutes % 60
        
        # Format the output
        start_time_str = f"{start_hour:02d}:{start_minute:02d}"
        end_time_str = f"{end_hour:02d}:{end_minute:02d}"
        
        print(f"Monday:{start_time_str}:{end_time_str}")
    else:
        print("No available time slot found")

if __name__ == "__main__":
    main()