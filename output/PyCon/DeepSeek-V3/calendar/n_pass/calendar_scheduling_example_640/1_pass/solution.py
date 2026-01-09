from constraint import Problem

def main():
    problem = Problem()
    
    # Define days as integers: 0 for Monday, 1 for Tuesday
    days = [0, 1]
    
    # Define time slots in minutes from 9:00 (540 minutes) to 17:00 (1020 minutes)
    start_min = 9 * 60  # 9:00 in minutes
    end_min = 17 * 60   # 17:00 in minutes
    
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Add variables for day and start time (in minutes from midnight)
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(start_min, end_min - meeting_duration + 1))
    
    # Bobby's busy times in minutes from midnight
    bobby_busy = [
        # Monday (day 0)
        [(14*60 + 30, 15*60)],  # 14:30-15:00
        # Tuesday (day 1)
        [(9*60, 11*60 + 30), (12*60, 12*60 + 30), (13*60, 15*60), (15*60 + 30, 17*60)]
    ]
    
    # Michael's busy times in minutes from midnight
    michael_busy = [
        # Monday (day 0)
        [(9*60, 10*60), (10*60 + 30, 13*60 + 30), (14*60, 15*60), (15*60 + 30, 17*60)],
        # Tuesday (day 1)
        [(9*60, 10*60 + 30), (11*60, 11*60 + 30), (12*60, 14*60), (15*60, 16*60), (16*60 + 30, 17*60)]
    ]
    
    def is_available(day, start_time):
        end_time = start_time + meeting_duration
        
        # Check Bobby's schedule
        for busy_start, busy_end in bobby_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check Michael's schedule
        for busy_start, busy_end in michael_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        return True
    
    problem.addConstraint(is_available, ['day', 'start_time'])
    
    # Find the earliest solution (minimize day and start_time)
    solutions = problem.getSolutions()
    
    if not solutions:
        print("No available time slot found")
        return
    
    # Find the earliest solution
    earliest_solution = min(solutions, key=lambda x: (x['day'], x['start_time']))
    
    day_num = earliest_solution['day']
    start_minutes = earliest_solution['start_time']
    end_minutes = start_minutes + meeting_duration
    
    # Convert to time strings
    start_hour = start_minutes // 60
    start_minute = start_minutes % 60
    end_hour = end_minutes // 60
    end_minute = end_minutes % 60
    
    day_name = "Monday" if day_num == 0 else "Tuesday"
    
    print(f"{day_name}: {start_hour:02d}:{start_minute:02d}-{end_hour:02d}:{end_minute:02d}")

if __name__ == "__main__":
    main()