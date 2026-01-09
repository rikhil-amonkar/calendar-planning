from constraint import Problem

def main():
    # Create problem instance
    problem = Problem()
    
    # Define days and time slots (in minutes from 9:00)
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Convert busy times to minutes from midnight for easier comparison
    natalie_busy = {
        'Monday': [(9*60, 9*60+30), (10*60, 12*60), (12*60+30, 13*60), 
                  (14*60, 14*60+30), (15*60, 16*60+30)],
        'Tuesday': [(9*60, 9*60+30), (10*60, 10*60+30), (12*60+30, 14*60), 
                   (16*60, 17*60)],
        'Wednesday': [(11*60, 11*60+30), (16*60, 16*60+30)],
        'Thursday': [(10*60, 11*60), (11*60+30, 15*60), (15*60+30, 16*60), 
                    (16*60+30, 17*60)]
    }
    
    william_busy = {
        'Monday': [(9*60+30, 11*60), (11*60+30, 17*60)],
        'Tuesday': [(9*60, 13*60), (13*60+30, 16*60)],
        'Wednesday': [(9*60, 12*60+30), (13*60, 14*60+30), (15*60+30, 16*60), 
                     (16*60+30, 17*60)],
        'Thursday': [(9*60, 10*60+30), (11*60, 11*60+30), (12*60, 12*60+30), 
                    (13*60, 14*60), (15*60, 17*60)]
    }
    
    # Add variables: day and start time (in minutes from 9:00)
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(work_start, work_end - 60 + 1))  # 1 hour meeting
    
    # Constraint: meeting must fit within work hours and avoid busy times
    def time_available(day, start_time):
        end_time = start_time + 60  # 1 hour meeting
        
        # Check Natalie's availability
        for busy_start, busy_end in natalie_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check William's availability  
        for busy_start, busy_end in william_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        return True
    
    problem.addConstraint(time_available, ['day', 'start_time'])
    
    # Find a solution
    solution = problem.getSolution()
    
    if solution:
        day = solution['day']
        start_minutes = solution['start_time']
        end_minutes = start_minutes + 60
        
        # Convert minutes to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"{day}")
        print(f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()