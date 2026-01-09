from constraint import Problem

def main():
    problem = Problem()
    
    # Define days and time slots (in minutes from 9:00)
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Add variables: day and start time (in minutes from 9:00)
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(work_start, work_end - 60 + 1))  # 1 hour meeting
    
    # Define busy times for Diane (in minutes from 9:00)
    diane_busy = {
        'Monday': [(12*60, 12*60+30), (15*60, 15*60+30)],
        'Tuesday': [(10*60, 11*60), (11*60+30, 12*60), (12*60+30, 13*60), (16*60, 17*60)],
        'Wednesday': [(9*60, 9*60+30), (14*60+30, 15*60), (16*60+30, 17*60)],
        'Thursday': [(15*60+30, 16*60+30)],
        'Friday': [(9*60+30, 11*60+30), (14*60+30, 15*60), (16*60, 17*60)]
    }
    
    # Define busy times for Matthew (in minutes from 9:00)
    matthew_busy = {
        'Monday': [(9*60, 10*60), (10*60+30, 17*60)],
        'Tuesday': [(9*60, 17*60)],
        'Wednesday': [(9*60, 11*60), (12*60, 14*60+30), (16*60, 17*60)],
        'Thursday': [(9*60, 16*60)],
        'Friday': [(9*60, 17*60)]
    }
    
    def is_available(day, start_time):
        end_time = start_time + 60  # 1 hour meeting
        
        # Check Diane's availability
        for busy_start, busy_end in diane_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Matthew's availability
        for busy_start, busy_end in matthew_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Matthew's preference: not Wednesday before 12:30
        if day == 'Wednesday' and start_time < 12*60 + 30:
            return False
        
        return True
    
    problem.addConstraint(is_available, ['day', 'start_time'])
    
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        day = solution['day']
        start_minutes = solution['start_time']
        end_minutes = start_minutes + 60
        
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