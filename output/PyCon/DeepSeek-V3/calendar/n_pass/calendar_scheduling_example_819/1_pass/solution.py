from constraint import Problem

def main():
    problem = Problem()
    
    # Define days and time slots in minutes from 9:00 (540 minutes) to 17:00 (1020 minutes)
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    start_min = 540  # 9:00 in minutes
    end_min = 1020   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Add variables: day and start time
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(start_min, end_min - meeting_duration + 1))
    
    # Define constraints
    def julie_constraint(day, start_time):
        # Julie has no meetings but wants to avoid Thursday before 11:30 (690 minutes)
        if day == 'Thursday' and start_time < 690:
            return False
        return True
    
    def ruth_constraint(day, start_time):
        end_time = start_time + meeting_duration
        # Ruth's busy periods converted to minutes
        busy_slots = {
            'Monday': [(540, 1020)],
            'Tuesday': [(540, 1020)],
            'Wednesday': [(540, 1020)],
            'Thursday': [(540, 690), (690, 870), (900, 1020)]  # 9:00-11:30, 11:30-14:30, 15:00-17:00
        }
        
        if day not in busy_slots:
            return True
            
        for busy_start, busy_end in busy_slots[day]:
            # Check if meeting overlaps with any busy period
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        return True
    
    problem.addConstraint(julie_constraint, ['day', 'start_time'])
    problem.addConstraint(ruth_constraint, ['day', 'start_time'])
    
    # Find a solution
    solution = problem.getSolution()
    
    if solution:
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