from constraint import Problem

def main():
    problem = Problem()
    
    # Define days and time slots in minutes from 9:00 (540 minutes)
    days = ['Monday', 'Tuesday', 'Wednesday']
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes
    
    # Roy's busy times in minutes from start of day
    roy_busy = {
        'Monday': [(10*60, 11*60+30), (12*60, 13*60), (14*60, 14*60+30), (15*60, 17*60)],
        'Tuesday': [(10*60+30, 11*60+30), (12*60, 14*60+30), (15*60, 15*60+30), (16*60, 17*60)],
        'Wednesday': [(9*60+30, 11*60+30), (12*60+30, 14*60), (14*60+30, 15*60+30), (16*60+30, 17*60)]
    }
    
    # Patrick is available all the time, so we only need to check Roy's schedule
    
    # Add variables: day and start time
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(work_start, work_end - meeting_duration + 1))
    
    # Constraint: meeting must fit within work hours and avoid Roy's busy times
    def meeting_constraint(day, start_time):
        end_time = start_time + meeting_duration
        
        # Check if meeting fits within work hours
        if start_time < work_start or end_time > work_end:
            return False
            
        # Check if meeting overlaps with any of Roy's busy times
        for busy_start, busy_end in roy_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
                
        return True
    
    problem.addConstraint(meeting_constraint, ['day', 'start_time'])
    
    # Find the earliest solution
    solutions = problem.getSolutions()
    
    if not solutions:
        print("No suitable time found")
        return
        
    # Sort solutions by day and start time to find earliest
    def solution_key(sol):
        day_order = {'Monday': 0, 'Tuesday': 1, 'Wednesday': 2}
        return (day_order[sol['day']], sol['start_time'])
    
    earliest_solution = min(solutions, key=solution_key)
    
    # Convert back to time format
    day = earliest_solution['day']
    start_minutes = earliest_solution['start_time']
    end_minutes = start_minutes + meeting_duration
    
    start_hour = start_minutes // 60
    start_minute = start_minutes % 60
    end_hour = end_minutes // 60
    end_minute = end_minutes % 60
    
    print(f"{day}:{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")

if __name__ == "__main__":
    main()