from constraint import Problem
import datetime

def main():
    problem = Problem()
    
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30
    
    # Define Terry's busy times in minutes from start of day
    terry_busy = {
        'Monday': [(10*60+30, 11*60), (12*60+30, 14*60), (15*60, 17*60)],
        'Tuesday': [(9*60+30, 10*60), (10*60+30, 11*60), (14*60, 14*60+30), (16*60, 16*60+30)],
        'Wednesday': [(9*60+30, 10*60+30), (11*60, 12*60), (13*60, 13*60+30), (15*60, 16*60), (16*60+30, 17*60)],
        'Thursday': [(9*60+30, 10*60), (12*60, 12*60+30), (13*60, 14*60+30), (16*60, 16*60+30)],
        'Friday': [(9*60, 11*60+30), (12*60, 12*60+30), (13*60+30, 16*60), (16*60+30, 17*60)]
    }
    
    # Define Frances's busy times in minutes from start of day
    frances_busy = {
        'Monday': [(9*60+30, 11*60), (11*60+30, 13*60), (14*60, 14*60+30), (15*60, 16*60)],
        'Tuesday': [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 12*60), (13*60, 14*60+30), (15*60+30, 16*60+30)],
        'Wednesday': [(9*60+30, 10*60), (10*60+30, 11*60), (11*60+30, 16*60), (16*60+30, 17*60)],
        'Thursday': [(11*60, 12*60+30), (14*60+30, 17*60)],
        'Friday': [(9*60+30, 10*60+30), (11*60, 12*60+30), (13*60, 16*60), (16*60+30, 17*60)]
    }
    
    # Add variables: day and start time (in minutes from work_start)
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(work_start, work_end - meeting_duration + 1))
    
    def is_available(day, start_time):
        end_time = start_time + meeting_duration
        
        # Check Terry's availability
        for busy_start, busy_end in terry_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Frances's availability
        for busy_start, busy_end in frances_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        return True
    
    problem.addConstraint(is_available, ['day', 'start_time'])
    
    # Find earliest available time, avoiding Tuesday if possible
    solutions = problem.getSolutions()
    
    if not solutions:
        print("No available time found")
        return
    
    # Sort solutions by day (avoiding Tuesday) and start time
    day_order = {'Monday': 0, 'Wednesday': 1, 'Thursday': 2, 'Friday': 3, 'Tuesday': 4}
    
    sorted_solutions = sorted(solutions, key=lambda s: (day_order[s['day']], s['start_time']))
    
    best_solution = sorted_solutions[0]
    
    day = best_solution['day']
    start_minutes = best_solution['start_time']
    end_minutes = start_minutes + meeting_duration
    
    # Convert to HH:MM format
    start_hours = start_minutes // 60
    start_mins = start_minutes % 60
    end_hours = end_minutes // 60
    end_mins = end_minutes % 60
    
    print(f"{day}:{start_hours:02d}:{start_mins:02d}:{end_hours:02d}:{end_mins:02d}")

if __name__ == "__main__":
    main()