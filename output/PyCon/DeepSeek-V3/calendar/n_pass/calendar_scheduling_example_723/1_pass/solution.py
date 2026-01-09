from constraint import Problem

def main():
    problem = Problem()
    
    # Define days and time slots (in minutes from 9:00)
    days = ['Monday', 'Tuesday', 'Wednesday']
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30
    
    # Convert schedules to minutes from midnight for easier computation
    arthur_busy = {
        'Monday': [(11*60, 11*60+30), (13*60+30, 14*60), (15*60, 15*60+30)],
        'Tuesday': [(13*60, 13*60+30), (16*60, 16*60+30)],
        'Wednesday': [(10*60, 10*60+30), (11*60, 11*60+30), (12*60, 12*60+30), (14*60, 14*60+30), (16*60, 16*60+30)]
    }
    
    michael_busy = {
        'Monday': [(9*60, 12*60), (12*60+30, 13*60), (14*60, 14*60+30), (15*60, 17*60)],
        'Tuesday': [(9*60+30, 11*60+30), (12*60, 13*60+30), (14*60, 15*60+30)],
        'Wednesday': [(10*60, 12*60+30), (13*60, 13*60+30)]
    }
    
    # Arthur cannot meet on Tuesday
    available_days = [day for day in days if day != 'Tuesday']
    
    # Add variables: day and start time (in minutes from 9:00)
    problem.addVariable('day', available_days)
    problem.addVariable('start_time', range(work_start, work_end - meeting_duration + 1))
    
    # Define constraint: meeting must fit within work hours and not conflict with busy times
    def meeting_constraint(day, start_time):
        end_time = start_time + meeting_duration
        
        # Check Arthur's schedule
        for busy_start, busy_end in arthur_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Michael's schedule
        for busy_start, busy_end in michael_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        return True
    
    problem.addConstraint(meeting_constraint, ['day', 'start_time'])
    
    # Find the earliest solution
    solutions = problem.getSolutions()
    
    if solutions:
        # Sort by day index and start time to find earliest
        day_order = {'Monday': 0, 'Tuesday': 1, 'Wednesday': 2}
        solutions.sort(key=lambda s: (day_order[s['day']], s['start_time']))
        
        best_solution = solutions[0]
        day = best_solution['day']
        start_minutes = best_solution['start_time']
        end_minutes = start_minutes + meeting_duration
        
        # Convert back to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"{day}")
        print(f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable meeting time found")

if __name__ == "__main__":
    main()