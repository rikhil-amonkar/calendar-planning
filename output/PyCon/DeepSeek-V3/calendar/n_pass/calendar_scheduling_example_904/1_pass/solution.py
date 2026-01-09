from constraint import Problem
import datetime

def main():
    problem = Problem()
    
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Daniel's busy times in minutes from start of day
    daniel_busy = {
        'Monday': [(9*60+30, 10*60+30), (12*60, 12*60+30), (13*60, 14*60), 
                  (14*60+30, 15*60), (15*60+30, 16*60)],
        'Tuesday': [(11*60, 12*60), (13*60, 13*60+30), (15*60+30, 16*60), 
                   (16*60+30, 17*60)],
        'Wednesday': [(9*60, 10*60), (14*60, 14*60+30)],
        'Thursday': [(10*60+30, 11*60), (12*60, 13*60), (14*60+30, 15*60), 
                    (15*60+30, 16*60)],
        'Friday': [(9*60, 9*60+30), (11*60+30, 12*60), (13*60, 13*60+30), 
                  (16*60+30, 17*60)]
    }
    
    # Bradley's busy times in minutes from start of day
    bradley_busy = {
        'Monday': [(9*60+30, 11*60), (11*60+30, 12*60), (12*60+30, 13*60), 
                  (14*60, 15*60)],
        'Tuesday': [(10*60+30, 11*60), (12*60, 13*60), (13*60+30, 14*60), 
                   (15*60+30, 16*60+30)],
        'Wednesday': [(9*60, 10*60), (11*60, 13*60), (13*60+30, 14*60), 
                     (14*60+30, 17*60)],
        'Thursday': [(9*60, 12*60+30), (13*60+30, 14*60), (14*60+30, 15*60), 
                    (15*60+30, 16*60+30)],
        'Friday': [(9*60, 9*60+30), (10*60, 12*60+30), (13*60, 13*60+30), 
                  (14*60, 14*60+30), (15*60+30, 16*60+30)]
    }
    
    # Add variables
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(work_start, work_end - 30 + 1))  # 30 min meeting
    
    # Constraints
    def time_available(day, start_time):
        end_time = start_time + 30
        
        # Daniel's preferences: not Wednesday, Thursday
        if day in ['Wednesday', 'Thursday']:
            return False
            
        # Bradley's preferences: not Monday, not Tuesday before 12:00, not Friday
        if day == 'Monday':
            return False
        if day == 'Tuesday' and start_time < 12*60:
            return False
        if day == 'Friday':
            return False
        
        # Check Daniel's availability
        for busy_start, busy_end in daniel_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Bradley's availability
        for busy_start, busy_end in bradley_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        return True
    
    problem.addConstraint(time_available, ['day', 'start_time'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
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