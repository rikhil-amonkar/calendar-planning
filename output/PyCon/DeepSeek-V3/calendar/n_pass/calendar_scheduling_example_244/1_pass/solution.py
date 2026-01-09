from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert all schedules to minutes since midnight
    # Walter: no meetings (free all day)
    walter_busy = []
    
    # Cynthia: 9:00-9:30, 10:00-10:30, 13:30-14:30, 15:00-16:00
    cynthia_busy = [
        (9*60, 9*60+30),   # 9:00-9:30
        (10*60, 10*60+30), # 10:00-10:30
        (13*60+30, 14*60+30), # 13:30-14:30
        (15*60, 16*60)     # 15:00-16:00
    ]
    
    # Ann: 10:00-11:00, 13:00-13:30, 14:00-15:00, 16:00-16:30
    ann_busy = [
        (10*60, 11*60),    # 10:00-11:00
        (13*60, 13*60+30), # 13:00-13:30
        (14*60, 15*60),    # 14:00-15:00
        (16*60, 16*60+30)  # 16:00-16:30
    ]
    
    # Catherine: 9:00-11:30, 12:30-13:30, 14:30-17:00
    catherine_busy = [
        (9*60, 11*60+30),  # 9:00-11:30
        (12*60+30, 13*60+30), # 12:30-13:30
        (14*60+30, 17*60)  # 14:30-17:00
    ]
    
    # Kyle: 9:00-9:30, 10:00-11:30, 12:00-12:30, 13:00-14:30, 15:00-16:00
    kyle_busy = [
        (9*60, 9*60+30),   # 9:00-9:30
        (10*60, 11*60+30), # 10:00-11:30
        (12*60, 12*60+30), # 12:00-12:30
        (13*60, 14*60+30), # 13:00-14:30
        (15*60, 16*60)     # 15:00-16:00
    ]
    
    # Define possible start times (every minute within work hours)
    possible_start_times = list(range(work_start, work_end - meeting_duration + 1))
    
    # Add variable for meeting start time
    problem.addVariable('start_time', possible_start_times)
    
    # Define constraint function to check if time works for all participants
    def time_works_for_all(start_time):
        end_time = start_time + meeting_duration
        
        # Check Walter (always available)
        # No need to check anything for Walter
        
        # Check Cynthia
        for busy_start, busy_end in cynthia_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Ann
        for busy_start, busy_end in ann_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Catherine
        for busy_start, busy_end in catherine_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Kyle
        for busy_start, busy_end in kyle_busy:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        return True
    
    problem.addConstraint(time_works_for_all, ['start_time'])
    
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
        time_range = f"{start_hour:02d}:{start_minute:02d}-{end_hour:02d}:{end_minute:02d}"
        day = "Monday"
        
        print(f"{time_range}")
        print(day)
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()