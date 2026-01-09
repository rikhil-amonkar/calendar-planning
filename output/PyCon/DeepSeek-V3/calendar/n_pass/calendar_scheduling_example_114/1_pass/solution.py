from constraint import Problem

def main():
    # Create a problem instance
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes
    
    # Convert all times to minutes since midnight for easier calculation
    # Stephanie's busy times
    stephanie_busy = [
        (10 * 60, 10 * 60 + 30),    # 10:00-10:30
        (16 * 60, 16 * 60 + 30)     # 16:00-16:30
    ]
    
    # Cheryl's busy times
    cheryl_busy = [
        (10 * 60, 10 * 60 + 30),    # 10:00-10:30
        (11 * 60 + 30, 12 * 60),    # 11:30-12:00
        (13 * 60 + 30, 14 * 60),    # 13:30-14:00
        (16 * 60 + 30, 17 * 60)     # 16:30-17:00
    ]
    
    # Bradley's busy times
    bradley_busy = [
        (9 * 60 + 30, 10 * 60),     # 9:30-10:00
        (10 * 60 + 30, 11 * 60 + 30), # 10:30-11:30
        (13 * 60 + 30, 14 * 60),    # 13:30-14:00
        (14 * 60 + 30, 15 * 60),    # 14:30-15:00
        (15 * 60 + 30, 17 * 60)     # 15:30-17:00
    ]
    
    # Steven's busy times
    steven_busy = [
        (9 * 60, 12 * 60),          # 9:00-12:00
        (13 * 60, 13 * 60 + 30),    # 13:00-13:30
        (14 * 60 + 30, 17 * 60)     # 14:30-17:00
    ]
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1, 15))
    
    # Add variable for meeting start time
    problem.addVariable('start_time', possible_starts)
    
    # Define constraint function to check if time works for all participants
    def time_works_for_all(start_time):
        end_time = start_time + meeting_duration
        
        # Check Stephanie's availability
        for busy_start, busy_end in stephanie_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Cheryl's availability
        for busy_start, busy_end in cheryl_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Bradley's availability
        for busy_start, busy_end in bradley_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Steven's availability
        for busy_start, busy_end in steven_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        return True
    
    # Add the constraint
    problem.addConstraint(time_works_for_all, ['start_time'])
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if solutions:
        # Get the first solution
        solution = solutions[0]
        start_minutes = solution['start_time']
        end_minutes = start_minutes + meeting_duration
        
        # Convert back to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format the output
        start_time_str = f"{start_hour:02d}:{start_minute:02d}"
        end_time_str = f"{end_hour:02d}:{end_minute:02d}"
        
        print(f"Monday:{start_time_str}:{end_time_str}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()