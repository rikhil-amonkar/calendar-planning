from constraint import Problem

def main():
    # Create problem instance
    problem = Problem()
    
    # Define days and time slots (in minutes from 9:00)
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes
    
    # Convert schedules to minutes from midnight for easier computation
    # Megan's schedule
    megan_busy = {
        'Monday': [(13*60, 13*60+30), (14*60, 15*60+30)],
        'Tuesday': [(9*60, 9*60+30), (12*60, 12*60+30), (16*60, 17*60)],
        'Wednesday': [(9*60+30, 10*60), (10*60+30, 11*60+30), (12*60+30, 14*60), (16*60, 16*60+30)],
        'Thursday': [(13*60+30, 14*60+30), (15*60, 15*60+30)]
    }
    
    # Daniel's schedule
    daniel_busy = {
        'Monday': [(10*60, 11*60+30), (12*60+30, 15*60)],
        'Tuesday': [(9*60, 10*60), (10*60+30, 17*60)],
        'Wednesday': [(9*60, 10*60), (10*60+30, 11*60+30), (12*60, 17*60)],
        'Thursday': [(9*60, 12*60), (12*60+30, 14*60+30), (15*60, 15*60+30), (16*60, 17*60)]
    }
    
    # Add variables: day and start time (in minutes from 9:00)
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(work_start, work_end - meeting_duration + 1))
    
    # Constraint: meeting must fit within work hours
    def within_work_hours(day, start_time):
        end_time = start_time + meeting_duration
        return start_time >= work_start and end_time <= work_end
    
    # Constraint: Megan must be available
    def megan_available(day, start_time):
        end_time = start_time + meeting_duration
        busy_times = megan_busy.get(day, [])
        for busy_start, busy_end in busy_times:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        return True
    
    # Constraint: Daniel must be available
    def daniel_available(day, start_time):
        end_time = start_time + meeting_duration
        busy_times = daniel_busy.get(day, [])
        for busy_start, busy_end in busy_times:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        return True
    
    # Add constraints
    problem.addConstraint(within_work_hours, ['day', 'start_time'])
    problem.addConstraint(megan_available, ['day', 'start_time'])
    problem.addConstraint(daniel_available, ['day', 'start_time'])
    
    # Find earliest solution (minimize start_time across all days)
    solutions = problem.getSolutions()
    if not solutions:
        print("No solution found")
        return
    
    # Find earliest solution
    earliest_solution = min(solutions, key=lambda s: (days.index(s['day']), s['start_time']))
    
    # Convert back to readable time format
    day = earliest_solution['day']
    start_minutes = earliest_solution['start_time']
    end_minutes = start_minutes + meeting_duration
    
    start_hour = start_minutes // 60
    start_minute = start_minutes % 60
    end_hour = end_minutes // 60
    end_minute = end_minutes % 60
    
    # Format output
    time_range = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
    print(f"{day}: {time_range}")

if __name__ == "__main__":
    main()