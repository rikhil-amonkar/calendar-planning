from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours in minutes from 9:00 (540) to 17:00 (1020)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30
    
    # Convert all times to minutes since midnight for easier calculation
    # Katherine's busy times
    katherine_busy = [
        (12 * 60, 12 * 60 + 30),      # 12:00-12:30
        (13 * 60, 14 * 60 + 30)       # 13:00-14:30
    ]
    
    # Rebecca has no meetings
    
    # Julie's busy times
    julie_busy = [
        (9 * 60, 9 * 60 + 30),        # 9:00-9:30
        (10 * 60 + 30, 11 * 60),      # 10:30-11:00
        (13 * 60 + 30, 14 * 60),      # 13:30-14:00
        (15 * 60, 15 * 60 + 30)       # 15:00-15:30
    ]
    
    # Angela's busy times
    angela_busy = [
        (9 * 60, 10 * 60),            # 9:00-10:00
        (10 * 60 + 30, 11 * 60),      # 10:30-11:00
        (11 * 60 + 30, 14 * 60),      # 11:30-14:00
        (14 * 60 + 30, 15 * 60),      # 14:30-15:00
        (16 * 60 + 30, 17 * 60)       # 16:30-17:00
    ]
    
    # Nicholas's busy times
    nicholas_busy = [
        (9 * 60 + 30, 11 * 60),       # 9:30-11:00
        (11 * 60 + 30, 13 * 60 + 30), # 11:30-13:30
        (14 * 60, 16 * 60),           # 14:00-16:00
        (16 * 60 + 30, 17 * 60)       # 16:30-17:00
    ]
    
    # Carl's busy times
    carl_busy = [
        (9 * 60, 11 * 60),            # 9:00-11:00
        (11 * 60 + 30, 12 * 60 + 30), # 11:30-12:30
        (13 * 60, 14 * 60 + 30),      # 13:00-14:30
        (15 * 60, 16 * 60),           # 15:00-16:00
        (16 * 60 + 30, 17 * 60)       # 16:30-17:00
    ]
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1, 15))
    
    # Add variable for meeting start time
    problem.addVariable("meeting_start", possible_starts)
    
    # Define constraint function to check if time works for everyone
    def time_works_for_all(meeting_start):
        meeting_end = meeting_start + meeting_duration
        
        # Check if meeting fits within work hours
        if meeting_end > work_end:
            return False
            
        # Angela's preference to avoid meetings before 15:00
        if meeting_end <= 15 * 60:
            return False
            
        # Check Katherine's availability
        for busy_start, busy_end in katherine_busy:
            if not (meeting_end <= busy_start or meeting_start >= busy_end):
                return False
                
        # Check Julie's availability
        for busy_start, busy_end in julie_busy:
            if not (meeting_end <= busy_start or meeting_start >= busy_end):
                return False
                
        # Check Angela's availability
        for busy_start, busy_end in angela_busy:
            if not (meeting_end <= busy_start or meeting_start >= busy_end):
                return False
                
        # Check Nicholas's availability
        for busy_start, busy_end in nicholas_busy:
            if not (meeting_end <= busy_start or meeting_start >= busy_end):
                return False
                
        # Check Carl's availability
        for busy_start, busy_end in carl_busy:
            if not (meeting_end <= busy_start or meeting_start >= busy_end):
                return False
                
        return True
    
    problem.addConstraint(time_works_for_all, ["meeting_start"])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        # Get the earliest solution
        solution = min(solutions, key=lambda x: x["meeting_start"])
        start_minutes = solution["meeting_start"]
        end_minutes = start_minutes + meeting_duration
        
        # Convert back to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"Monday:{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()