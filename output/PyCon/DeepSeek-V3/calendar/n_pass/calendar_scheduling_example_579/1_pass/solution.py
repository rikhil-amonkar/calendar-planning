from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert schedules to minutes since midnight
    christine_busy = [
        (11 * 60, 11 * 60 + 30),    # 11:00-11:30
        (15 * 60, 15 * 60 + 30)     # 15:00-15:30
    ]
    
    helen_busy = [
        (9 * 60 + 30, 10 * 60 + 30),  # 9:30-10:30
        (11 * 60, 11 * 60 + 30),      # 11:00-11:30
        (12 * 60, 12 * 60 + 30),      # 12:00-12:30
        (13 * 60 + 30, 16 * 60),      # 13:30-16:00
        (16 * 60 + 30, 17 * 60)       # 16:30-17:00
    ]
    
    # Helen cannot meet after 15:00
    helen_no_meet_after = 15 * 60
    
    # Possible start times (in minutes from midnight)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1, 15))
    
    problem.addVariable("start_time", possible_starts)
    
    def is_valid_time(start_time):
        end_time = start_time + meeting_duration
        
        # Check Christine's availability
        for busy_start, busy_end in christine_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Helen's availability
        for busy_start, busy_end in helen_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Helen's constraint: cannot meet after 15:00
        if start_time >= helen_no_meet_after:
            return False
        
        return True
    
    problem.addConstraint(is_valid_time, ["start_time"])
    
    solutions = problem.getSolutions()
    
    if solutions:
        # Take the first solution
        start_minutes = solutions[0]["start_time"]
        end_minutes = start_minutes + meeting_duration
        
        # Convert back to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
        print("Monday")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()