from constraint import Problem
import datetime

def main():
    problem = Problem()
    
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Brian's busy times in minutes from midnight for each day
    brian_busy = {
        'Monday': [(9*60+30, 10*60), (12*60+30, 14*60+30), (15*60+30, 16*60)],
        'Tuesday': [(9*60, 9*60+30)],
        'Wednesday': [(12*60+30, 14*60), (16*60+30, 17*60)],
        'Thursday': [(11*60, 11*60+30), (13*60, 13*60+30), (16*60+30, 17*60)],
        'Friday': [(9*60+30, 10*60), (10*60+30, 11*60), (13*60, 13*60+30), (15*60, 16*60), (16*60+30, 17*60)]
    }
    
    # Julia's busy times in minutes from midnight for each day
    julia_busy = {
        'Monday': [(9*60, 10*60), (11*60, 11*60+30), (12*60+30, 13*60), (15*60+30, 16*60)],
        'Tuesday': [(13*60, 14*60), (16*60, 16*60+30)],
        'Wednesday': [(9*60, 11*60+30), (12*60, 12*60+30), (13*60, 17*60)],
        'Thursday': [(9*60, 10*60+30), (11*60, 17*60)],
        'Friday': [(9*60, 10*60), (10*60+30, 11*60+30), (12*60+30, 14*60), (14*60+30, 15*60), (15*60+30, 16*60)]
    }
    
    # Define variables: day and start time (in minutes from midnight)
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(work_start, work_end - 60))  # 1 hour meeting
    
    # Constraint: meeting must fit within work hours
    def within_work_hours(day, start_time):
        return start_time >= work_start and start_time + 60 <= work_end
    
    # Constraint: meeting must not conflict with Brian's schedule
    def brian_available(day, start_time):
        end_time = start_time + 60
        for busy_start, busy_end in brian_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        return True
    
    # Constraint: meeting must not conflict with Julia's schedule
    def julia_available(day, start_time):
        end_time = start_time + 60
        for busy_start, busy_end in julia_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        return True
    
    # Constraint: Brian prefers to avoid Monday
    def avoid_monday(day, start_time):
        if day == 'Monday':
            # Only allow Monday if no other days are available
            # This will be handled by finding earliest availability
            return True
        return True
    
    problem.addConstraint(within_work_hours, ['day', 'start_time'])
    problem.addConstraint(brian_available, ['day', 'start_time'])
    problem.addConstraint(julia_available, ['day', 'start_time'])
    problem.addConstraint(avoid_monday, ['day', 'start_time'])
    
    # Find all solutions and pick the earliest one
    solutions = problem.getSolutions()
    
    if solutions:
        # Sort solutions by day (Monday to Friday) and then by start time
        day_order = {day: i for i, day in enumerate(days)}
        solutions.sort(key=lambda s: (day_order[s['day']], s['start_time']))
        
        # Try to avoid Monday if possible
        best_solution = None
        for solution in solutions:
            if solution['day'] != 'Monday':
                best_solution = solution
                break
        
        # If no non-Monday solution found, use the first available (which might be Monday)
        if not best_solution:
            best_solution = solutions[0]
        
        day = best_solution['day']
        start_minutes = best_solution['start_time']
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