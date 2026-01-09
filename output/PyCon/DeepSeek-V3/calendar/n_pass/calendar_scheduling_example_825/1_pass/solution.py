from constraint import Problem
import datetime

def main():
    problem = Problem()
    
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Convert busy times to minutes since midnight
    laura_busy = {
        'Monday': [(10*60+30, 11*60), (12*60+30, 13*60), (14*60+30, 15*60+30), (16*60, 17*60)],
        'Tuesday': [(9*60+30, 10*60), (11*60, 11*60+30), (13*60, 13*60+30), (14*60+30, 15*60), (16*60, 17*60)],
        'Wednesday': [(11*60+30, 12*60), (12*60+30, 13*60), (15*60+30, 16*60+30)],
        'Thursday': [(10*60+30, 11*60), (12*60, 13*60+30), (15*60, 15*60+30), (16*60, 16*60+30)]
    }
    
    philip_busy = {
        'Monday': [(9*60, 17*60)],
        'Tuesday': [(9*60, 11*60), (11*60+30, 12*60), (13*60, 13*60+30), (14*60, 14*60+30), (15*60, 16*60+30)],
        'Wednesday': [(9*60, 10*60), (11*60, 12*60), (12*60+30, 16*60), (16*60+30, 17*60)],
        'Thursday': [(9*60, 10*60+30), (11*60, 12*60+30), (13*60, 17*60)]
    }
    
    # Philip cannot meet on Wednesday
    available_days = ['Monday', 'Tuesday', 'Thursday']
    
    meeting_duration = 60  # 1 hour in minutes
    
    # Add variables
    problem.addVariable('day', available_days)
    problem.addVariable('start_time', range(work_start, work_end - meeting_duration + 1))
    
    def time_conflict(day, start_time):
        end_time = start_time + meeting_duration
        
        # Check Laura's schedule
        for busy_start, busy_end in laura_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Philip's schedule  
        for busy_start, busy_end in philip_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        return True
    
    problem.addConstraint(time_conflict, ['day', 'start_time'])
    
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        day = solution['day']
        start_minutes = solution['start_time']
        end_minutes = start_minutes + meeting_duration
        
        # Convert to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"{day}:{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()