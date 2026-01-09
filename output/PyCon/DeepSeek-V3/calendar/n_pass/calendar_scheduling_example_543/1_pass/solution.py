from constraint import Problem

def main():
    # Create problem instance
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes
    
    # Convert schedules to minutes from midnight
    james_busy = [
        (11 * 60 + 30, 12 * 60),      # 11:30-12:00
        (14 * 60 + 30, 15 * 60)       # 14:30-15:00
    ]
    
    john_busy = [
        (9 * 60 + 30, 11 * 60),       # 9:30-11:00
        (11 * 60 + 30, 12 * 60),      # 11:30-12:00
        (12 * 60 + 30, 13 * 60 + 30), # 12:30-13:30
        (14 * 60 + 30, 16 * 60 + 30)  # 14:30-16:30
    ]
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_starts = range(work_start, work_end - meeting_duration + 1, 15)
    
    # Add variable for meeting start time
    problem.addVariable('start_time', possible_starts)
    
    # Add constraint: meeting must fit within work hours
    def within_work_hours(start):
        return start >= work_start and start + meeting_duration <= work_end
    
    problem.addConstraint(within_work_hours, ['start_time'])
    
    # Add constraint: James must be available
    def james_available(start):
        end = start + meeting_duration
        for busy_start, busy_end in james_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        return True
    
    problem.addConstraint(james_available, ['start_time'])
    
    # Add constraint: John must be available
    def john_available(start):
        end = start + meeting_duration
        for busy_start, busy_end in john_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        return True
    
    problem.addConstraint(john_available, ['start_time'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if solutions:
        # Get the first solution
        start_time_minutes = solutions[0]['start_time']
        end_time_minutes = start_time_minutes + meeting_duration
        
        # Convert to HH:MM format
        start_hour = start_time_minutes // 60
        start_minute = start_time_minutes % 60
        end_hour = end_time_minutes // 60
        end_minute = end_time_minutes % 60
        
        # Format output
        start_str = f"{start_hour:02d}:{start_minute:02d}"
        end_str = f"{end_hour:02d}:{end_minute:02d}"
        
        print(f"Monday:{start_str}:{end_str}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()