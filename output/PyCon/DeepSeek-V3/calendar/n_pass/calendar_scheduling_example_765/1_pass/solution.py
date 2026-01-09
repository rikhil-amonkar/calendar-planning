from constraint import Problem

def main():
    problem = Problem()
    
    # Define days (Monday=0, Tuesday=1, Wednesday=2)
    days = [0, 1, 2]
    
    # Define time slots in minutes from 9:00 (540) to 17:00 (1020)
    # Meeting duration is 30 minutes
    start_times = list(range(540, 1020 - 30 + 1, 30))  # 30-minute intervals
    
    # Add variables: day and start_time
    problem.addVariable('day', days)
    problem.addVariable('start_time', start_times)
    
    # Joshua's busy times (in minutes from start of day)
    joshua_busy = [
        # Monday (day 0)
        [(15*60, 15*60+30)],  # 15:00-15:30
        # Tuesday (day 1)  
        [(11*60+30, 12*60), (13*60, 13*60+30), (14*60+30, 15*60)],
        # Wednesday (day 2) - no meetings
        []
    ]
    
    # Joyce's busy times (in minutes from start of day)
    joyce_busy = [
        # Monday (day 0)
        [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 12*60+30), 
         (13*60, 15*60), (15*60+30, 17*60)],
        # Tuesday (day 1)
        [(9*60, 17*60)],  # All day busy
        # Wednesday (day 2)
        [(9*60, 9*60+30), (10*60, 11*60), (12*60+30, 15*60+30), 
         (16*60, 16*60+30)]
    ]
    
    def time_conflict_constraint(day, start_time):
        end_time = start_time + 30  # 30-minute meeting
        
        # Check Joshua's schedule
        for busy_start, busy_end in joshua_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Joyce's schedule  
        for busy_start, busy_end in joyce_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Joyce's preference: not Monday before 12:00
        if day == 0 and end_time <= 12*60:
            return False
            
        return True
    
    problem.addConstraint(time_conflict_constraint, ['day', 'start_time'])
    
    # Find a solution
    solution = problem.getSolution()
    
    if solution:
        day_num = solution['day']
        start_minutes = solution['start_time']
        end_minutes = start_minutes + 30
        
        day_names = ['Monday', 'Tuesday', 'Wednesday']
        day_name = day_names[day_num]
        
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"{day_name}: {start_hour:02d}:{start_minute:02d}-{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()