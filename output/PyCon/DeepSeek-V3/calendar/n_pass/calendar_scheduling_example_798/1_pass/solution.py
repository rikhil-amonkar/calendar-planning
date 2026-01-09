from constraint import Problem

def main():
    problem = Problem()
    
    # Define days and time slots in minutes from 9:00 (540 minutes) to 17:00 (1020 minutes)
    days = ['Monday', 'Tuesday', 'Wednesday']
    start_min = 540  # 9:00 in minutes
    end_min = 1020   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Add variables: day and start time
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(start_min, end_min - meeting_duration + 1))
    
    # Define busy times for Nancy and Jose in minutes from start of day
    nancy_busy = {
        'Monday': [(600, 630), (690, 750), (810, 840), (870, 930), (960, 1020)],
        'Tuesday': [(570, 630), (660, 690), (720, 750), (780, 810), (930, 960)],
        'Wednesday': [(600, 690), (810, 960)]
    }
    
    jose_busy = {
        'Monday': [(540, 1020)],
        'Tuesday': [(540, 1020)],
        'Wednesday': [(540, 570), (600, 750), (810, 870), (900, 1020)]
    }
    
    def is_available(day, start_time):
        end_time = start_time + meeting_duration
        
        # Check Nancy's availability
        for busy_start, busy_end in nancy_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Jose's availability
        for busy_start, busy_end in jose_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        return True
    
    problem.addConstraint(is_available, ['day', 'start_time'])
    
    # Find the earliest solution (minimize day index and start time)
    solutions = problem.getSolutions()
    
    if not solutions:
        print("No available time slot found")
        return
    
    # Sort solutions by day (Monday first) and then by start time
    day_order = {'Monday': 0, 'Tuesday': 1, 'Wednesday': 2}
    sorted_solutions = sorted(solutions, key=lambda x: (day_order[x['day']], x['start_time']))
    
    # Get the earliest solution
    earliest = sorted_solutions[0]
    day = earliest['day']
    start_minutes = earliest['start_time']
    end_minutes = start_minutes + meeting_duration
    
    # Convert minutes to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    start_time_str = minutes_to_time(start_minutes)
    end_time_str = minutes_to_time(end_minutes)
    
    print(f"{day}:{start_time_str}:{end_time_str}")

if __name__ == "__main__":
    main()