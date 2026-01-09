from constraint import Problem

def main():
    # Create a problem instance
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Meeting duration in minutes
    meeting_duration = 60
    
    # Convert schedules to minutes since midnight
    # Danielle's meetings
    danielle_meetings = [
        (9 * 60, 10 * 60),      # 9:00-10:00
        (10 * 60 + 30, 11 * 60), # 10:30-11:00
        (14 * 60 + 30, 15 * 60), # 14:30-15:00
        (15 * 60 + 30, 16 * 60), # 15:30-16:00
        (16 * 60 + 30, 17 * 60)  # 16:30-17:00
    ]
    
    # Bruce's meetings
    bruce_meetings = [
        (11 * 60, 11 * 60 + 30),     # 11:00-11:30
        (12 * 60 + 30, 13 * 60),     # 12:30-13:00
        (14 * 60, 14 * 60 + 30),     # 14:00-14:30
        (15 * 60 + 30, 16 * 60)      # 15:30-16:00
    ]
    
    # Eric's meetings
    eric_meetings = [
        (9 * 60, 9 * 60 + 30),       # 9:00-9:30
        (10 * 60, 11 * 60),          # 10:00-11:00
        (11 * 60 + 30, 13 * 60),     # 11:30-13:00
        (14 * 60 + 30, 15 * 60 + 30) # 14:30-15:30
    ]
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1, 15))
    
    # Add variable for meeting start time
    problem.addVariable('start_time', possible_starts)
    
    # Define constraint function
    def is_time_available(start_time):
        end_time = start_time + meeting_duration
        
        # Check if meeting fits within work hours
        if start_time < work_start or end_time > work_end:
            return False
        
        # Check Danielle's availability
        for meeting_start, meeting_end in danielle_meetings:
            if not (end_time <= meeting_start or start_time >= meeting_end):
                return False
        
        # Check Bruce's availability
        for meeting_start, meeting_end in bruce_meetings:
            if not (end_time <= meeting_start or start_time >= meeting_end):
                return False
        
        # Check Eric's availability
        for meeting_start, meeting_end in eric_meetings:
            if not (end_time <= meeting_start or start_time >= meeting_end):
                return False
        
        return True
    
    # Add constraint
    problem.addConstraint(is_time_available, ['start_time'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        # Get the first solution
        start_time_minutes = solutions[0]['start_time']
        
        # Convert back to time format
        start_hour = start_time_minutes // 60
        start_minute = start_time_minutes % 60
        
        end_time_minutes = start_time_minutes + meeting_duration
        end_hour = end_time_minutes // 60
        end_minute = end_time_minutes % 60
        
        # Format output
        print(f"Monday:{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No available time slot found")

if __name__ == "__main__":
    main()