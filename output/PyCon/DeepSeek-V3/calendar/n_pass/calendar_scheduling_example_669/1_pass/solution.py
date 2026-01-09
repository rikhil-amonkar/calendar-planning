from constraint import Problem

def main():
    problem = Problem()
    
    # Define days and time slots in minutes from 9:00 (540 minutes) to 17:00 (1020 minutes)
    days = ['Monday', 'Tuesday']
    start_min = 9 * 60  # 9:00 in minutes
    end_min = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Add variables for day and start time
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(start_min, end_min - meeting_duration + 1))
    
    # Define busy times for Jean and Doris in minutes
    jean_busy = [
        # Tuesday 11:30-12:00, 16:00-16:30
        ('Tuesday', 11*60+30, 12*60),
        ('Tuesday', 16*60, 16*60+30)
    ]
    
    doris_busy = [
        # Monday 9:00-11:30, 12:00-12:30, 13:30-16:00, 16:30-17:00
        ('Monday', 9*60, 11*60+30),
        ('Monday', 12*60, 12*60+30),
        ('Monday', 13*60+30, 16*60),
        ('Monday', 16*60+30, 17*60),
        # Tuesday 9:00-17:00
        ('Tuesday', 9*60, 17*60)
    ]
    
    def is_available(day, start_time):
        end_time = start_time + meeting_duration
        
        # Check Jean's schedule
        for busy_day, busy_start, busy_end in jean_busy:
            if busy_day == day:
                if not (end_time <= busy_start or start_time >= busy_end):
                    return False
        
        # Check Doris's schedule
        for busy_day, busy_start, busy_end in doris_busy:
            if busy_day == day:
                if not (end_time <= busy_start or start_time >= busy_end):
                    return False
        
        # Doris prefers not to meet on Monday after 14:00
        if day == 'Monday' and start_time >= 14*60:
            return False
            
        return True
    
    problem.addConstraint(is_available, ['day', 'start_time'])
    
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        day = solution['day']
        start_minutes = solution['start_time']
        end_minutes = start_minutes + meeting_duration
        
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"{day}: {start_hour:02d}:{start_minute:02d}-{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()