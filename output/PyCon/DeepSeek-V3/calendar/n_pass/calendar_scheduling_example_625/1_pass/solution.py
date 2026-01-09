from constraint import Problem

def main():
    problem = Problem()
    
    # Define days and time slots in minutes from 9:00 (540 minutes) to 17:00 (1020 minutes)
    days = ['Monday', 'Tuesday']
    start_min = 540  # 9:00 in minutes
    end_min = 1020   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Add variables: day and start time (in minutes from midnight)
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(start_min, end_min - meeting_duration + 1))
    
    # Define constraints
    
    # Jeffrey is free entire week - no constraints needed
    
    # Harold's blocked times (in minutes from midnight)
    harold_blocked = {
        'Monday': [(540, 600), (630, 1020)],  # 9:00-10:00, 10:30-17:00
        'Tuesday': [(540, 570), (630, 690), (750, 810), (870, 930), (960, 1020)]  # 9:00-9:30, 10:30-11:30, 12:30-13:30, 14:30-15:30, 16:00-17:00
    }
    
    # Harold's preferences: avoid Monday, avoid Tuesday before 14:30 (870 minutes)
    def harold_constraint(day, start_time):
        end_time = start_time + meeting_duration
        
        # Check if overlaps with any blocked time on that day
        if day in harold_blocked:
            for block_start, block_end in harold_blocked[day]:
                if not (end_time <= block_start or start_time >= block_end):
                    return False
        
        # Preference constraints (soft constraints handled as hard for simplicity)
        if day == 'Monday':
            return False  # Harold wants to avoid Monday
        if day == 'Tuesday' and end_time <= 870:  # Before 14:30
            return False
            
        return True
    
    problem.addConstraint(harold_constraint, ['day', 'start_time'])
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        day = solution['day']
        start_minutes = solution['start_time']
        end_minutes = start_minutes + meeting_duration
        
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