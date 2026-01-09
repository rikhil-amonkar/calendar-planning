from constraint import Problem

def main():
    problem = Problem()
    
    # Define days and time slots (in minutes from 9:00)
    days = ['Monday', 'Tuesday', 'Wednesday']
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30
    
    # Convert busy times to minutes from midnight for each day
    tyler_busy = {
        'Tuesday': [(9*60, 9*60+30), (14*60+30, 15*60)],
        'Wednesday': [(10*60+30, 11*60), (12*60+30, 13*60), (13*60+30, 14*60), (16*60+30, 17*60)]
    }
    
    ruth_busy = {
        'Monday': [(9*60, 10*60), (10*60+30, 12*60), (12*60+30, 14*60+30), (15*60, 16*60), (16*60+30, 17*60)],
        'Tuesday': [(9*60, 17*60)],
        'Wednesday': [(9*60, 17*60)]
    }
    
    # Add variables: day and start time (in minutes from 9:00)
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(work_start, work_end - meeting_duration + 1))
    
    def time_conflict(day, start_time):
        end_time = start_time + meeting_duration
        
        # Check Tyler's constraints
        if day in tyler_busy:
            for busy_start, busy_end in tyler_busy[day]:
                if not (end_time <= busy_start or start_time >= busy_end):
                    return False
        
        # Check Ruth's constraints
        if day in ruth_busy:
            for busy_start, busy_end in ruth_busy[day]:
                if not (end_time <= busy_start or start_time >= busy_end):
                    return False
        
        # Tyler's preference: avoid Monday before 16:00
        if day == 'Monday' and end_time <= 16 * 60:
            return False
            
        return True
    
    problem.addConstraint(time_conflict, ['day', 'start_time'])
    
    # Find a solution
    solution = problem.getSolution()
    
    if solution:
        day = solution['day']
        start_minutes = solution['start_time']
        end_minutes = start_minutes + meeting_duration
        
        # Convert minutes to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"{day}:{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()