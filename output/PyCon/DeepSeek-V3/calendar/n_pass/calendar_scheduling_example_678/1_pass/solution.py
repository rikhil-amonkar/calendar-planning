from constraint import Problem

def main():
    problem = Problem()
    
    # Define days (Monday=0, Tuesday=1)
    days = [0, 1]
    
    # Define time slots in minutes from 9:00 (540 minutes) to 17:00 (1020 minutes)
    # Meeting duration: 1 hour = 60 minutes
    start_times = list(range(540, 1020 - 60 + 1, 15))  # 15-minute intervals
    
    # Add variables: day and start_time
    problem.addVariable('day', days)
    problem.addVariable('start_time', start_times)
    
    # Russell's constraints
    def russell_constraint(day, start_time):
        end_time = start_time + 60
        
        # Monday constraints
        if day == 0:  # Monday
            # Busy: 10:30-11:00 (630-660 minutes)
            if start_time < 660 and end_time > 630:
                return False
        # Tuesday constraints  
        elif day == 1:  # Tuesday
            # Busy: 13:00-13:30 (780-810 minutes)
            if start_time < 810 and end_time > 780:
                return False
            # Preference: rather not meet before 13:30 (810 minutes)
            if end_time <= 810:
                return False
        return True
    
    # Alexander's constraints
    def alexander_constraint(day, start_time):
        end_time = start_time + 60
        
        # Monday constraints
        if day == 0:  # Monday
            # Busy: 9:00-11:30 (540-690 minutes)
            if start_time < 690 and end_time > 540:
                return False
            # Busy: 12:00-14:30 (720-870 minutes)
            if start_time < 870 and end_time > 720:
                return False
            # Busy: 15:00-17:00 (900-1020 minutes)
            if start_time < 1020 and end_time > 900:
                return False
        # Tuesday constraints
        elif day == 1:  # Tuesday
            # Busy: 9:00-10:00 (540-600 minutes)
            if start_time < 600 and end_time > 540:
                return False
            # Busy: 13:00-14:00 (780-840 minutes)
            if start_time < 840 and end_time > 780:
                return False
            # Busy: 15:00-15:30 (900-930 minutes)
            if start_time < 930 and end_time > 900:
                return False
            # Busy: 16:00-16:30 (960-990 minutes)
            if start_time < 990 and end_time > 960:
                return False
        return True
    
    # Add constraints
    problem.addConstraint(russell_constraint, ['day', 'start_time'])
    problem.addConstraint(alexander_constraint, ['day', 'start_time'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        day = solution['day']
        start_minutes = solution['start_time']
        end_minutes = start_minutes + 60
        
        # Convert minutes to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        day_name = "Monday" if day == 0 else "Tuesday"
        
        print(f"{day_name}")
        print(f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()