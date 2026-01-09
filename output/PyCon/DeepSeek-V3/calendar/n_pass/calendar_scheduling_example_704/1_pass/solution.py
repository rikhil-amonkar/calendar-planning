from constraint import Problem

def main():
    problem = Problem()
    
    # Define days (Monday=0, Tuesday=1, Wednesday=2)
    days = [0, 1, 2]
    
    # Define time slots in minutes from 9:00 (540 minutes) to 17:00 (1020 minutes)
    # 30 minute meeting means we need start times from 9:00 to 16:30
    start_times = list(range(540, 990 + 1, 30))  # 9:00 to 16:30 in 30-min increments
    
    # Add variables
    problem.addVariable("day", days)
    problem.addVariable("start_time", start_times)
    
    # Samuel's busy times (in minutes from start of day)
    samuel_busy = {
        0: [(630, 660), (720, 750), (780, 900), (930, 990)],  # Monday
        1: [(540, 720), (840, 930), (990, 1020)],  # Tuesday
        2: [(630, 660), (690, 720), (750, 780), (840, 870), (900, 960)]  # Wednesday
    }
    
    # Larry has no meetings, so no constraints from his calendar
    
    def time_constraint(day, start_time):
        end_time = start_time + 30
        
        # Check if meeting fits within work hours (9:00-17:00)
        if start_time < 540 or end_time > 1020:
            return False
        
        # Check Samuel's availability
        if day in samuel_busy:
            for busy_start, busy_end in samuel_busy[day]:
                # Check for overlap
                if not (end_time <= busy_start or start_time >= busy_end):
                    return False
        
        # Larry prefers not Wednesday (day=2)
        if day == 2:
            return False
        
        # Samuel prefers to avoid Tuesday (day=1)
        if day == 1:
            return False
        
        return True
    
    problem.addConstraint(time_constraint, ["day", "start_time"])
    
    # Find earliest solution
    solutions = problem.getSolutions()
    
    if solutions:
        # Sort by day and start_time to find earliest
        solutions.sort(key=lambda x: (x["day"], x["start_time"]))
        best_solution = solutions[0]
        
        day_num = best_solution["day"]
        start_minutes = best_solution["start_time"]
        end_minutes = start_minutes + 30
        
        # Convert minutes to HH:MM format
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"
        
        start_time_str = minutes_to_time(start_minutes)
        end_time_str = minutes_to_time(end_minutes)
        
        day_names = ["Monday", "Tuesday", "Wednesday"]
        day_str = day_names[day_num]
        
        print(f"{day_str}:{start_time_str}:{end_time_str}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()