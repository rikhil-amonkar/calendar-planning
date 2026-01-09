from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Albert's busy times in minutes from midnight
    albert_busy = [
        (9 * 60, 10 * 60),      # 9:00-10:00
        (10 * 60 + 30, 12 * 60), # 10:30-12:00
        (15 * 60, 16 * 60 + 30) # 15:00-16:30
    ]
    
    # Albert cannot meet after 11:00
    albert_no_meet_after = 11 * 60
    
    # Define possible start times (in 15-minute intervals for efficiency)
    possible_starts = []
    for minute in range(work_start, work_end - meeting_duration + 1, 15):
        possible_starts.append(minute)
    
    problem.addVariable("start_time", possible_starts)
    
    # Constraints
    def albert_available(start_time):
        end_time = start_time + meeting_duration
        
        # Check if meeting ends after 11:00 constraint
        if start_time >= albert_no_meet_after:
            return False
            
        # Check if meeting overlaps with any busy period
        for busy_start, busy_end in albert_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        return True
    
    problem.addConstraint(albert_available, ["start_time"])
    
    # Solve
    solutions = problem.getSolutions()
    
    if solutions:
        # Take the first solution
        start_minutes = solutions[0]["start_time"]
        end_minutes = start_minutes + meeting_duration
        
        # Convert to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"Monday:{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()