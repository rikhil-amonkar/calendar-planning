from constraint import Problem

def main():
    # Create problem instance
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Convert busy times to minutes since midnight
    patrick_busy = [
        (9*60, 9*60+30),    # 9:00-9:30
        (10*60, 10*60+30),  # 10:00-10:30
        (13*60+30, 14*60),  # 13:30-14:00
        (16*60, 16*60+30)   # 16:00-16:30
    ]
    
    kayla_busy = [
        (12*60+30, 13*60+30),  # 12:30-13:30
        (15*60, 15*60+30),     # 15:00-15:30
        (16*60, 16*60+30)      # 16:00-16:30
    ]
    
    carl_busy = [
        (10*60+30, 11*60),     # 10:30-11:00
        (12*60, 12*60+30),     # 12:00-12:30
        (13*60, 13*60+30),     # 13:00-13:30
        (14*60+30, 17*60)      # 14:30-17:00
    ]
    
    christian_busy = [
        (9*60, 12*60+30),      # 9:00-12:30
        (13*60, 14*60),        # 13:00-14:00
        (14*60+30, 17*60)      # 14:30-17:00
    ]
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1, 15))
    
    # Add variable for meeting start time
    problem.addVariable('start_time', possible_starts)
    
    # Define constraint function
    def is_time_available(start_time):
        end_time = start_time + meeting_duration
        
        # Check if meeting fits within work hours
        if end_time > work_end:
            return False
        
        # Check Patrick's availability
        for busy_start, busy_end in patrick_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Kayla's availability
        for busy_start, busy_end in kayla_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Carl's availability
        for busy_start, busy_end in carl_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Christian's availability
        for busy_start, busy_end in christian_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        return True
    
    # Add constraint
    problem.addConstraint(is_time_available, ['start_time'])
    
    # Find solution
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