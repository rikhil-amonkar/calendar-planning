from constraint import Problem

def main():
    problem = Problem()
    
    # Define days (Monday=0, Tuesday=1, Wednesday=2)
    days = [0, 1, 2]
    
    # Define time slots in minutes from 9:00 (540 minutes) to 17:00 (1020 minutes)
    # 30 minute meeting means we need start times from 9:00 to 16:30
    start_times = list(range(540, 990, 30))  # 9:00 to 16:30 in 30-min increments
    
    # Add variables
    problem.addVariable('day', days)
    problem.addVariable('start_time', start_times)
    
    # Define busy periods for each person (in minutes from midnight)
    # Cheryl's busy periods
    cheryl_busy = [
        # Monday
        (540, 570), (690, 780), (930, 960),
        # Tuesday  
        (900, 930)
    ]
    
    # Kyle's busy periods
    kyle_busy = [
        # Monday (entire day)
        (540, 1020),
        # Tuesday (9:30 to 17:00)
        (570, 1020),
        # Wednesday
        (540, 570), (600, 780), (810, 840), (870, 1020)
    ]
    
    def is_available(day, start_time):
        end_time = start_time + 30
        
        # Cheryl cannot meet on Wednesday (day 2)
        if day == 2:
            return False
            
        # Check Cheryl's schedule
        for busy_start, busy_end in cheryl_busy:
            # Convert to absolute time based on day
            abs_busy_start = busy_start + (day * 1440)
            abs_busy_end = busy_end + (day * 1440)
            abs_meeting_start = start_time + (day * 1440)
            abs_meeting_end = end_time + (day * 1440)
            
            # Check for overlap
            if not (abs_meeting_end <= abs_busy_start or abs_meeting_start >= abs_busy_end):
                return False
        
        # Check Kyle's schedule
        for busy_start, busy_end in kyle_busy:
            # Convert to absolute time based on day
            abs_busy_start = busy_start + (day * 1440)
            abs_busy_end = busy_end + (day * 1440)
            abs_meeting_start = start_time + (day * 1440)
            abs_meeting_end = end_time + (day * 1440)
            
            # Check for overlap
            if not (abs_meeting_end <= abs_busy_start or abs_meeting_start >= abs_busy_end):
                return False
                
        return True
    
    problem.addConstraint(is_available, ['day', 'start_time'])
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        day_num = solution['day']
        start_minutes = solution['start_time']
        end_minutes = start_minutes + 30
        
        # Convert minutes to time format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        day_names = ['Monday', 'Tuesday', 'Wednesday']
        day_name = day_names[day_num]
        
        print(f"{day_name}:{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()