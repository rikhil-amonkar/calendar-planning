from z3 import *

def main():
    # Convert time to minutes since midnight
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes

    # Define busy intervals in minutes for each participant per day
    ryan_busy = [
        [(time_to_minutes("09:30"), time_to_minutes("10:00")), 
         (time_to_minutes("11:00"), time_to_minutes("12:00")), 
         (time_to_minutes("13:00"), time_to_minutes("13:30")), 
         (time_to_minutes("15:30"), time_to_minutes("16:00"))],  # Monday
        [(time_to_minutes("11:30"), time_to_minutes("12:30")), 
         (time_to_minutes("15:30"), time_to_minutes("16:00"))]   # Tuesday
    ]
    
    adam_busy = [
        [(time_to_minutes("09:00"), time_to_minutes("10:30")), 
         (time_to_minutes("11:00"), time_to_minutes("13:30")), 
         (time_to_minutes("14:00"), time_to_minutes("16:00")), 
         (time_to_minutes("16:30"), time_to_minutes("17:00"))],  # Monday
        [(time_to_minutes("09:00"), time_to_minutes("10:00")), 
         (time_to_minutes("10:30"), time_to_minutes("15:30")), 
         (time_to_minutes("16:00"), time_to_minutes("17:00"))]   # Tuesday
    ]

    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    work_start = 540
    work_end = 1020
    meeting_duration = 30

    # Z3 variables
    day = Int('day')
    start_time = Int('start_time')
    
    solver = Solver()
    
    # Day must be Monday (0) or Tuesday (1)
    solver.add(day >= 0, day <= 1)
    # Meeting must fit within work hours
    solver.add(start_time >= work_start, start_time + meeting_duration <= work_end)
    
    # Add constraints for Ryan's busy intervals
    for d in range(2):
        for busy_start, busy_end in ryan_busy[d]:
            solver.add(Implies(day == d, 
                              Or(start_time + meeting_duration <= busy_start, 
                                 start_time >= busy_end)))
    
    # Add constraints for Adam's busy intervals
    for d in range(2):
        for busy_start, busy_end in adam_busy[d]:
            solver.add(Implies(day == d, 
                              Or(start_time + meeting_duration <= busy_start, 
                                 start_time >= busy_end)))
    
    # Adam's preference: Avoid Monday before 14:30 (870 minutes)
    preference = Or(day != 0, start_time >= time_to_minutes("14:30"))
    
    # First try with preference
    solver.push()
    solver.add(preference)
    if solver.check() == sat:
        model = solver.model()
    else:
        # If unsatisfiable, relax preference
        solver.pop()
        solver.check()
        model = solver.model()
    
    # Extract solution
    day_val = model[day].as_long()
    start_minutes = model[start_time].as_long()
    end_minutes = start_minutes + meeting_duration
    
    # Convert minutes back to time strings
    def minutes_to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"
    
    start_str = minutes_to_time(start_minutes)
    end_str = minutes_to_time(end_minutes)
    day_str = "Monday" if day_val == 0 else "Tuesday"
    
    print(f"{day_str} {start_str}:{end_str}")

if __name__ == "__main__":
    main()