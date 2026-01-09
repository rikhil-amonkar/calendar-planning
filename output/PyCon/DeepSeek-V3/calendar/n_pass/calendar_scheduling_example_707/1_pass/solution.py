from constraint import Problem

def main():
    problem = Problem()
    
    # Define days and time slots (in minutes from 9:00)
    days = ['Monday', 'Tuesday', 'Wednesday']
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert schedules to minutes from 9:00
    ryan_busy = {
        'Monday': [(9*60+30, 10*60), (11*60, 12*60), (13*60, 13*60+30), (15*60+30, 16*60)],
        'Tuesday': [(11*60+30, 12*60+30), (15*60+30, 16*60)],
        'Wednesday': [(12*60, 13*60), (15*60+30, 16*60), (16*60+30, 17*60)]
    }
    
    adam_busy = {
        'Monday': [(9*60, 10*60+30), (11*60, 13*60+30), (14*60, 16*60), (16*60+30, 17*60)],
        'Tuesday': [(9*60, 10*60), (10*60+30, 15*60+30), (16*60, 17*60)],
        'Wednesday': [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 14*60+30), (15*60, 15*60+30), (16*60, 16*60+30)]
    }
    
    # Ryan cannot meet on Wednesday
    available_days = ['Monday', 'Tuesday']
    
    # Adam wants to avoid Monday before 14:30
    adam_monday_avoid = 14 * 60 + 30  # 14:30 in minutes
    
    # Add variables: day and start time
    problem.addVariable('day', available_days)
    problem.addVariable('start_time', range(work_start, work_end - meeting_duration + 1))
    
    def time_conflict(day, start_time):
        end_time = start_time + meeting_duration
        
        # Check Ryan's schedule
        for busy_start, busy_end in ryan_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Adam's schedule  
        for busy_start, busy_end in adam_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Adam's preference: avoid Monday before 14:30
        if day == 'Monday' and end_time <= adam_monday_avoid:
            return False
            
        return True
    
    problem.addConstraint(time_conflict, ['day', 'start_time'])
    
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        day = solution['day']
        start_minutes = solution['start_time']
        end_minutes = start_minutes + meeting_duration
        
        # Convert back to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"{day}:{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()