from constraint import Problem

def main():
    problem = Problem()
    
    # Define days and time slots (in minutes from 9:00)
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Convert busy times to minutes from midnight for each day
    carl_busy = {
        'Monday': [(11*60, 11*60+30)],
        'Tuesday': [(14*60+30, 15*60)],
        'Wednesday': [(10*60, 11*60+30), (13*60, 13*60+30)],
        'Thursday': [(13*60+30, 14*60), (16*60, 16*60+30)]
    }
    
    margaret_busy = {
        'Monday': [(9*60, 10*60+30), (11*60, 17*60)],
        'Tuesday': [(9*60+30, 12*60), (13*60+30, 14*60), (15*60+30, 17*60)],
        'Wednesday': [(9*60+30, 12*60), (12*60+30, 13*60), (13*60+30, 14*60+30), (15*60, 17*60)],
        'Thursday': [(10*60, 12*60), (12*60+30, 14*60), (14*60+30, 17*60)]
    }
    
    # Add variables: day and start time (in minutes from 9:00)
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(0, (work_end - work_start) - 60 + 1))  # 60 min meeting
    
    # Constraint: Meeting must fit within work hours
    def within_work_hours(day, start_time):
        actual_start = work_start + start_time
        actual_end = actual_start + 60
        return actual_end <= work_end
    
    # Constraint: Meeting must not conflict with Carl's schedule
    def carl_available(day, start_time):
        actual_start = work_start + start_time
        actual_end = actual_start + 60
        
        if day not in carl_busy:
            return True
            
        for busy_start, busy_end in carl_busy[day]:
            if not (actual_end <= busy_start or actual_start >= busy_end):
                return False
        return True
    
    # Constraint: Meeting must not conflict with Margaret's schedule
    def margaret_available(day, start_time):
        actual_start = work_start + start_time
        actual_end = actual_start + 60
        
        if day not in margaret_busy:
            return True
            
        for busy_start, busy_end in margaret_busy[day]:
            if not (actual_end <= busy_start or actual_start >= busy_end):
                return False
        return True
    
    # Constraint: Carl prefers to avoid Thursday
    def avoid_thursday(day, start_time):
        return day != 'Thursday'
    
    # Add constraints
    problem.addConstraint(within_work_hours, ['day', 'start_time'])
    problem.addConstraint(carl_available, ['day', 'start_time'])
    problem.addConstraint(margaret_available, ['day', 'start_time'])
    problem.addConstraint(avoid_thursday, ['day', 'start_time'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        # Use the first solution found
        solution = solutions[0]
        day = solution['day']
        start_minutes = work_start + solution['start_time']
        end_minutes = start_minutes + 60
        
        # Convert to HH:MM format
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