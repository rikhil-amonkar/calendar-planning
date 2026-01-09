from constraint import Problem

def main():
    # Create problem instance
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes
    
    # Convert blocked times to minutes since midnight
    # Olivia: 12:30-13:30, 14:30-15:00, 16:30-17:00
    olivia_blocked = [
        (12*60 + 30, 13*60 + 30),
        (14*60 + 30, 15*60 + 0),
        (16*60 + 30, 17*60 + 0)
    ]
    
    # Anna: no meetings
    anna_blocked = []
    
    # Virginia: 9:00-10:00, 11:30-16:00, 16:30-17:00
    virginia_blocked = [
        (9*60 + 0, 10*60 + 0),
        (11*60 + 30, 16*60 + 0),
        (16*60 + 30, 17*60 + 0)
    ]
    
    # Paul: 9:00-9:30, 11:00-11:30, 13:00-14:00, 14:30-16:00, 16:30-17:00
    paul_blocked = [
        (9*60 + 0, 9*60 + 30),
        (11*60 + 0, 11*60 + 30),
        (13*60 + 0, 14*60 + 0),
        (14*60 + 30, 16*60 + 0),
        (16*60 + 30, 17*60 + 0)
    ]
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1, 15))
    
    # Add variable for meeting start time
    problem.addVariable('start_time', possible_starts)
    
    # Define constraint function
    def time_available(start, blocked_times, duration):
        end = start + duration
        for block_start, block_end in blocked_times:
            # Check if meeting overlaps with any blocked time
            if not (end <= block_start or start >= block_end):
                return False
        return True
    
    # Add constraints for each participant
    problem.addConstraint(
        lambda start: time_available(start, olivia_blocked, meeting_duration),
        ['start_time']
    )
    problem.addConstraint(
        lambda start: time_available(start, anna_blocked, meeting_duration),
        ['start_time']
    )
    problem.addConstraint(
        lambda start: time_available(start, virginia_blocked, meeting_duration),
        ['start_time']
    )
    problem.addConstraint(
        lambda start: time_available(start, paul_blocked, meeting_duration),
        ['start_time']
    )
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if solutions:
        # Take the first solution
        start_minutes = solutions[0]['start_time']
        end_minutes = start_minutes + meeting_duration
        
        # Convert to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format output
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        print(f"Monday:{start_time}:{end_time}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()