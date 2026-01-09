from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert all times to minutes since midnight
    # Juan's busy periods
    juan_busy = [
        (9 * 60, 10 * 60 + 30),    # 9:00-10:30
        (15 * 60 + 30, 16 * 60)    # 15:30-16:00
    ]
    
    # Marilyn's busy periods
    marilyn_busy = [
        (11 * 60, 11 * 60 + 30),   # 11:00-11:30
        (12 * 60 + 30, 13 * 60)    # 12:30-13:00
    ]
    
    # Ronald's busy periods
    ronald_busy = [
        (9 * 60, 10 * 60 + 30),    # 9:00-10:30
        (12 * 60, 12 * 60 + 30),   # 12:00-12:30
        (13 * 60, 13 * 60 + 30),   # 13:00-13:30
        (14 * 60, 16 * 60 + 30)    # 14:00-16:30
    ]
    
    # Juan cannot meet after 16:00
    juan_cutoff = 16 * 60
    
    # Define possible meeting start times (in minutes since midnight)
    meeting_start = range(work_start, work_end - meeting_duration + 1)
    
    problem.addVariable("meeting_start", meeting_start)
    
    def is_available(meeting_start, busy_periods, cutoff_time=None):
        meeting_end = meeting_start + meeting_duration
        
        # Check if meeting would extend beyond cutoff time
        if cutoff_time and meeting_end > cutoff_time:
            return False
            
        # Check if meeting overlaps with any busy period
        for busy_start, busy_end in busy_periods:
            if not (meeting_end <= busy_start or meeting_start >= busy_end):
                return False
        return True
    
    def juan_constraint(meeting_start):
        return is_available(meeting_start, juan_busy, juan_cutoff)
    
    def marilyn_constraint(meeting_start):
        return is_available(meeting_start, marilyn_busy)
    
    def ronald_constraint(meeting_start):
        return is_available(meeting_start, ronald_busy)
    
    problem.addConstraint(juan_constraint, ["meeting_start"])
    problem.addConstraint(marilyn_constraint, ["meeting_start"])
    problem.addConstraint(ronald_constraint, ["meeting_start"])
    
    solutions = problem.getSolutions()
    
    if solutions:
        # Take the first solution
        meeting_start_minutes = solutions[0]["meeting_start"]
        
        # Convert back to time format
        start_hour = meeting_start_minutes // 60
        start_minute = meeting_start_minutes % 60
        
        end_minutes = meeting_start_minutes + meeting_duration
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format output
        time_range = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        day = "Monday"
        
        print(f"{time_range}")
        print(f"{day}")
    else:
        print("No suitable meeting time found")

if __name__ == "__main__":
    main()