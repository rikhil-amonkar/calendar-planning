from constraint import Problem

def main():
    # Define the problem
    problem = Problem()
    
    # Work hours: 9:00 to 17:00 (9:00-17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Meeting duration: 30 minutes
    meeting_duration = 30
    
    # Convert schedules to minutes since midnight
    bradley_busy = [
        (9*60 + 30, 10*60),      # 9:30-10:00
        (12*60 + 30, 13*60),     # 12:30-13:00
        (13*60 + 30, 14*60),     # 13:30-14:00
        (15*60 + 30, 16*60)      # 15:30-16:00
    ]
    
    teresa_busy = [
        (10*60 + 30, 11*60),     # 10:30-11:00
        (12*60, 12*60 + 30),     # 12:00-12:30
        (13*60, 13*60 + 30),     # 13:00-13:30
        (14*60 + 30, 15*60)      # 14:30-15:00
    ]
    
    elizabeth_busy = [
        (9*60, 9*60 + 30),       # 9:00-9:30
        (10*60 + 30, 11*60 + 30), # 10:30-11:30
        (13*60, 13*60 + 30),     # 13:00-13:30
        (14*60 + 30, 15*60),     # 14:30-15:00
        (15*60 + 30, 17*60)      # 15:30-17:00
    ]
    
    christian_busy = [
        (9*60, 9*60 + 30),       # 9:00-9:30
        (10*60 + 30, 17*60)      # 10:30-17:00
    ]
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_start_times = []
    for minute in range(work_start, work_end - meeting_duration + 1, 15):
        possible_start_times.append(minute)
    
    # Add variable for start time
    problem.addVariable('start_time', possible_start_times)
    
    # Define constraint function
    def time_available(start_time):
        end_time = start_time + meeting_duration
        
        # Check if within work hours
        if start_time < work_start or end_time > work_end:
            return False
        
        # Check Bradley's availability
        for busy_start, busy_end in bradley_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Teresa's availability
        for busy_start, busy_end in teresa_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Elizabeth's availability
        for busy_start, busy_end in elizabeth_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Christian's availability
        for busy_start, busy_end in christian_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        return True
    
    # Add constraint
    problem.addConstraint(time_available, ['start_time'])
    
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
        
        # Format the output
        time_range = f"{start_hour:02d}:{start_minute:02d}-{end_hour:02d}:{end_minute:02d}"
        print(f"Monday: {time_range}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()