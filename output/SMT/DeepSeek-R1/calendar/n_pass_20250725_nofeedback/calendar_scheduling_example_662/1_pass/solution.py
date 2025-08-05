from z3 import *

def main():
    # Convert time string to minutes from 9:00
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hours = int(parts[0])
        minutes = int(parts[1])
        return (hours - 9) * 60 + minutes

    # Blocked intervals for Gary and David on Monday and Tuesday
    gary_intervals = {
        0: [('9:30', '10:00'), ('11:00', '13:00'), ('14:00', '14:30'), ('16:30', '17:00')],
        1: [('9:00', '9:30'), ('10:30', '11:00'), ('14:30', '16:00')]
    }
    
    david_intervals = {
        0: [('9:00', '9:30'), ('10:00', '13:00'), ('14:30', '16:30')],
        1: [('9:00', '9:30'), ('10:00', '10:30'), ('11:00', '12:30'), ('13:00', '14:30'), ('15:00', '16:00'), ('16:30', '17:00')]
    }
    
    # Convert the intervals to minutes
    gary_minutes = {}
    david_minutes = {}
    
    for day in [0, 1]:
        gary_minutes[day] = []
        for start_str, end_str in gary_intervals[day]:
            start_min = time_to_minutes(start_str)
            end_min = time_to_minutes(end_str)
            gary_minutes[day].append((start_min, end_min))
            
    for day in [0, 1]:
        david_minutes[day] = []
        for start_str, end_str in david_intervals[day]:
            start_min = time_to_minutes(start_str)
            end_min = time_to_minutes(end_str)
            david_minutes[day].append((start_min, end_min))
    
    # Set up Z3 solver
    solver = Solver()
    day_var = Int('day')
    start_var = Int('start')
    
    # Day must be 0 (Monday) or 1 (Tuesday)
    solver.add(Or(day_var == 0, day_var == 1))
    # Start time must be between 0 and 420 minutes (since 17:00 is 480 minutes, and meeting duration is 60 minutes)
    solver.add(start_var >= 0)
    solver.add(start_var <= 420)
    
    # Add constraints for Gary and David's blocked times
    for day in [0, 1]:
        for b_start, b_end in gary_minutes[day]:
            # The meeting [start, start+60) must not overlap with [b_start, b_end)
            solver.add(Implies(day_var == day, Or(start_var + 60 <= b_start, start_var >= b_end)))
        for b_start, b_end in david_minutes[day]:
            solver.add(Implies(day_var == day, Or(start_var + 60 <= b_start, start_var >= b_end)))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        day_val = model[day_var].as_long()
        start_minutes = model[start_var].as_long()
        
        # Convert day_val to day string
        day_str = "Monday" if day_val == 0 else "Tuesday"
        
        # Convert start_minutes to time string (HH:MM)
        total_minutes_start = start_minutes
        hours_start = 9 + total_minutes_start // 60
        minutes_start = total_minutes_start % 60
        start_time = f"{hours_start:02d}:{minutes_start:02d}"
        
        # Calculate end time (start + 60 minutes)
        total_minutes_end = start_minutes + 60
        hours_end = 9 + total_minutes_end // 60
        minutes_end = total_minutes_end % 60
        end_time = f"{hours_end:02d}:{minutes_end:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()