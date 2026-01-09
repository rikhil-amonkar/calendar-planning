from constraint import Problem
import datetime

def main():
    problem = Problem()
    
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Convert busy times to minutes since midnight
    betty_busy = {
        'Monday': [(10*60, 10*60+30), (13*60+30, 14*60), (15*60, 15*60+30), (16*60, 16*60+30)],
        'Tuesday': [(9*60, 9*60+30), (11*60+30, 12*60), (12*60+30, 13*60), (13*60+30, 14*60), (16*60+30, 17*60)],
        'Wednesday': [(9*60+30, 10*60+30), (13*60, 13*60+30), (14*60, 14*60+30)],
        'Thursday': [(9*60+30, 10*60), (11*60+30, 12*60), (14*60, 14*60+30), (15*60, 15*60+30), (16*60+30, 17*60)]
    }
    
    scott_busy = {
        'Monday': [(9*60+30, 15*60), (15*60+30, 16*60), (16*60+30, 17*60)],
        'Tuesday': [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 12*60), (12*60+30, 13*60+30), (14*60, 15*60), (16*60, 16*60+30)],
        'Wednesday': [(9*60+30, 12*60+30), (13*60, 13*60+30), (14*60, 14*60+30), (15*60, 15*60+30), (16*60, 16*60+30)],
        'Thursday': [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 12*60), (12*60+30, 13*60), (15*60, 16*60), (16*60+30, 17*60)]
    }
    
    # Add variables: day and start time (in minutes from midnight)
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(work_start, work_end - 30 + 1))  # 30 min meeting
    
    # Constraints
    def time_conflict(day, start_time):
        end_time = start_time + 30
        
        # Betty cannot meet on Monday
        if day == 'Monday':
            return False
            
        # Betty cannot meet on Tuesday or Thursday before 15:00
        if day in ['Tuesday', 'Thursday'] and start_time < 15 * 60:
            return False
            
        # Scott prefers to avoid Wednesday (but will accept if necessary)
        # Check if meeting conflicts with Betty's schedule
        for busy_start, busy_end in betty_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
                
        # Check if meeting conflicts with Scott's schedule
        for busy_start, busy_end in scott_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
                
        return True
    
    problem.addConstraint(time_conflict, ['day', 'start_time'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        # Prefer non-Wednesday days if possible
        non_wednesday_solutions = [s for s in solutions if s['day'] != 'Wednesday']
        if non_wednesday_solutions:
            solution = non_wednesday_solutions[0]
        else:
            solution = solutions[0]
        
        day = solution['day']
        start_minutes = solution['start_time']
        end_minutes = start_minutes + 30
        
        # Convert to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        start_time_str = f"{start_hour:02d}:{start_minute:02d}"
        end_time_str = f"{end_hour:02d}:{end_minute:02d}"
        
        print(f"{day}")
        print(f"{start_time_str}:{end_time_str}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()