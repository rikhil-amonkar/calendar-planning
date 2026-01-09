from constraint import Problem
import datetime

def main():
    # Define work hours and days
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    
    # Convert schedules to minutes from midnight
    nicole_busy = {
        'Tuesday': [(16*60, 16*60+30)],
        'Wednesday': [(15*60, 15*60+30)],
        'Friday': [(12*60, 12*60+30), (15*60+30, 16*60)]
    }
    
    daniel_busy = {
        'Monday': [(9*60, 12*60+30), (13*60, 13*60+30), (14*60, 16*60+30)],
        'Tuesday': [(9*60, 10*60+30), (11*60+30, 12*60+30), (13*60, 13*60+30), (15*60, 16*60), (16*60+30, 17*60)],
        'Wednesday': [(9*60, 10*60), (11*60, 12*60+30), (13*60, 13*60+30), (14*60, 14*60+30), (16*60+30, 17*60)],
        'Thursday': [(11*60, 12*60), (13*60, 14*60), (15*60, 15*60+30)],
        'Friday': [(10*60, 11*60), (11*60+30, 12*60), (12*60+30, 14*60+30), (15*60, 15*60+30), (16*60, 16*60+30)]
    }
    
    # Create problem
    problem = Problem()
    
    # Variables: day index and start time (in minutes from work_start)
    problem.addVariable('day', range(len(days)))
    problem.addVariable('start_time', range(work_start, work_end - 60 + 1))  # 1 hour meeting
    
    # Constraint: meeting must fit within work hours and avoid busy times
    def meeting_constraint(day_idx, start_time):
        day = days[day_idx]
        end_time = start_time + 60
        
        # Check Nicole's availability
        if day in nicole_busy:
            for busy_start, busy_end in nicole_busy[day]:
                if not (end_time <= busy_start or start_time >= busy_end):
                    return False
        
        # Check Daniel's availability  
        if day in daniel_busy:
            for busy_start, busy_end in daniel_busy[day]:
                if not (end_time <= busy_start or start_time >= busy_end):
                    return False
        
        return True
    
    problem.addConstraint(meeting_constraint, ['day', 'start_time'])
    
    # Find earliest solution (minimize day and start_time)
    solutions = problem.getSolutions()
    
    if not solutions:
        print("No solution found")
        return
    
    # Find earliest solution
    earliest_solution = min(solutions, key=lambda sol: (sol['day'], sol['start_time']))
    
    day_idx = earliest_solution['day']
    start_minutes = earliest_solution['start_time']
    end_minutes = start_minutes + 60
    
    # Convert to time format
    start_time_str = f"{start_minutes // 60:02d}:{start_minutes % 60:02d}"
    end_time_str = f"{end_minutes // 60:02d}:{end_minutes % 60:02d}"
    day_str = days[day_idx]
    
    print(f"{day_str}: {start_time_str}-{end_time_str}")

if __name__ == "__main__":
    main()