from constraint import Problem

def main():
    # Create problem instance
    problem = Problem()
    
    # Define work hours (9:00 to 17:00 in minutes from start of day)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Define busy times for each person in minutes from start of day
    # Cynthia's busy times
    cynthia_busy = [
        (9*60 + 30, 10*60 + 30),   # 9:30-10:30
        (11*60 + 30, 12*60),       # 11:30-12:00
        (13*60, 13*60 + 30),       # 13:00-13:30
        (15*60, 16*60)             # 15:00-16:00
    ]
    
    # Lauren's busy times
    lauren_busy = [
        (9*60, 9*60 + 30),         # 9:00-9:30
        (10*60 + 30, 11*60),       # 10:30-11:00
        (11*60 + 30, 12*60),       # 11:30-12:00
        (13*60, 13*60 + 30),       # 13:00-13:30
        (14*60, 14*60 + 30),       # 14:00-14:30
        (15*60, 15*60 + 30),       # 15:00-15:30
        (16*60, 17*60)             # 16:00-17:00
    ]
    
    # Robert's busy times
    robert_busy = [
        (10*60 + 30, 11*60),       # 10:30-11:00
        (11*60 + 30, 12*60),       # 11:30-12:00
        (12*60 + 30, 13*60 + 30),  # 12:30-13:30
        (14*60, 16*60)             # 14:00-16:00
    ]
    
    # Define possible start times (every minute within work hours)
    possible_start_times = list(range(work_start, work_end - meeting_duration + 1))
    
    # Add variable for meeting start time
    problem.addVariable('start_time', possible_start_times)
    
    # Add constraint: meeting must not overlap with anyone's busy times
    def no_overlap(start_time):
        meeting_end = start_time + meeting_duration
        
        # Check Cynthia's schedule
        for busy_start, busy_end in cynthia_busy:
            if not (meeting_end <= busy_start or start_time >= busy_end):
                return False
        
        # Check Lauren's schedule
        for busy_start, busy_end in lauren_busy:
            if not (meeting_end <= busy_start or start_time >= busy_end):
                return False
        
        # Check Robert's schedule
        for busy_start, busy_end in robert_busy:
            if not (meeting_end <= busy_start or start_time >= busy_end):
                return False
        
        return True
    
    problem.addConstraint(no_overlap, ['start_time'])
    
    # Find earliest solution
    solutions = problem.getSolutions()
    
    if solutions:
        # Find earliest start time
        earliest_solution = min(solutions, key=lambda x: x['start_time'])
        start_time_minutes = earliest_solution['start_time']
        end_time_minutes = start_time_minutes + meeting_duration
        
        # Convert to HH:MM format
        start_hour = start_time_minutes // 60
        start_minute = start_time_minutes % 60
        end_hour = end_time_minutes // 60
        end_minute = end_time_minutes % 60
        
        # Format output
        start_time_str = f"{start_hour:02d}:{start_minute:02d}"
        end_time_str = f"{end_hour:02d}:{end_minute:02d}"
        
        print(f"Monday:{start_time_str}:{end_time_str}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()