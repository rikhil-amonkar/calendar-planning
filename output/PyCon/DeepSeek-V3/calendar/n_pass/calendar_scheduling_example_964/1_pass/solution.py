from constraint import Problem
import datetime

def main():
    problem = Problem()
    
    # Define days and time slots (in minutes from 9:00 to 17:00)
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    start_times = [9 * 60 + i * 30 for i in range(16)]  # 9:00 to 16:30 in 30-min increments
    
    # Add variables
    problem.addVariable('day', days)
    problem.addVariable('start_time', start_times)
    
    # Betty cannot meet on Wednesday or Thursday
    def day_constraint(day, start_time):
        return day not in ['Wednesday', 'Thursday']
    
    # Define busy times for Betty (in minutes from 0:00)
    betty_busy = {
        'Monday': [(10*60, 10*60+30), (11*60+30, 12*60+30), (16*60, 16*60+30)],
        'Tuesday': [(9*60+30, 10*60), (10*60+30, 11*60), (12*60, 12*60+30), (13*60+30, 15*60), (16*60+30, 17*60)],
        'Wednesday': [(13*60+30, 14*60), (14*60+30, 15*60)],
        'Friday': [(9*60, 10*60), (11*60+30, 12*60), (12*60+30, 13*60), (14*60+30, 15*60)]
    }
    
    # Define busy times for Megan (in minutes from 0:00)
    megan_busy = {
        'Monday': [(9*60, 17*60)],
        'Tuesday': [(9*60, 9*60+30), (10*60, 10*60+30), (12*60, 14*60), (15*60, 15*60+30), (16*60, 16*60+30)],
        'Wednesday': [(9*60+30, 10*60+30), (11*60, 11*60+30), (12*60+30, 13*60), (13*60+30, 14*60+30), (15*60+30, 17*60)],
        'Thursday': [(9*60, 10*60+30), (11*60+30, 14*60), (14*60+30, 15*60), (15*60+30, 16*60+30)],
        'Friday': [(9*60, 17*60)]
    }
    
    def time_constraint(day, start_time):
        duration = 60  # 1 hour meeting
        
        # Check if meeting fits within work hours
        end_time = start_time + duration
        if end_time > 17 * 60:
            return False
        
        # Check Betty's availability
        if day in betty_busy:
            for busy_start, busy_end in betty_busy[day]:
                if not (end_time <= busy_start or start_time >= busy_end):
                    return False
        
        # Check Megan's availability
        if day in megan_busy:
            for busy_start, busy_end in megan_busy[day]:
                if not (end_time <= busy_start or start_time >= busy_end):
                    return False
        
        return True
    
    problem.addConstraint(day_constraint, ['day', 'start_time'])
    problem.addConstraint(time_constraint, ['day', 'start_time'])
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        day = solution['day']
        start_minutes = solution['start_time']
        
        # Convert minutes to time format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format output
        time_range = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print(f"{day}: {time_range}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()