from constraint import Problem

def main():
    # Define the problem
    problem = Problem()
    
    # Work hours: 9:00 to 17:00 (9 to 17 hours)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Meeting duration: 1 hour = 60 minutes
    meeting_duration = 60
    
    # Convert blocked times to minutes since midnight
    kayla_blocked = [
        (10 * 60, 10 * 60 + 30),      # 10:00-10:30
        (14 * 60 + 30, 16 * 60)       # 14:30-16:00
    ]
    
    rebecca_blocked = [
        (9 * 60, 13 * 60),            # 9:00-13:00
        (13 * 60 + 30, 15 * 60),      # 13:30-15:00
        (15 * 60 + 30, 16 * 60)       # 15:30-16:00
    ]
    
    # Define possible start times (in minutes from midnight)
    # Start time must allow for the full meeting duration within work hours
    possible_start_times = list(range(work_start, work_end - meeting_duration + 1, 15))
    
    # Add variable for start time
    problem.addVariable('start_time', possible_start_times)
    
    # Define constraint function
    def is_time_available(start_time):
        end_time = start_time + meeting_duration
        
        # Check if meeting fits within work hours
        if start_time < work_start or end_time > work_end:
            return False
        
        # Check Kayla's availability
        for block_start, block_end in kayla_blocked:
            if not (end_time <= block_start or start_time >= block_end):
                return False
        
        # Check Rebecca's availability
        for block_start, block_end in rebecca_blocked:
            if not (end_time <= block_start or start_time >= block_end):
                return False
        
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