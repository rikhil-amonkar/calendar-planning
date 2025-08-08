from z3 import *

def main():
    # Convert time string to minutes from 9:00
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return (hour - 9) * 60 + minute

    # Convert minutes from 9:00 back to HH:MM format (24-hour)
    def minutes_to_time(minutes):
        total_minutes = 9 * 60 + minutes
        h = total_minutes // 60
        m = total_minutes % 60
        return f"{h:02d}:{m:02d}"

    # Busy intervals for each participant
    stephanie_busy = [
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ]
    
    cheryl_busy = [
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    
    bradley_busy = [
        (time_to_minutes("9:30"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:30")),
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("17:00"))
    ]
    
    steven_busy = [
        (time_to_minutes("9:00"), time_to_minutes("12:00")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("17:00"))
    ]
    
    # Create Z3 solver and variable for start time (in minutes from 9:00)
    s = Int('start_time')
    solver = Solver()
    
    # Meeting must be within 9:00 to 17:00 and last 60 minutes
    solver.add(s >= 0)
    solver.add(s <= 420)  # 420 minutes from 9:00 is 16:00 (since 16:00 + 1 hour = 17:00)
    
    # Add constraints for each participant's busy intervals
    for interval in stephanie_busy:
        b_start, b_end = interval
        solver.add(Or(s + 60 <= b_start, s >= b_end))
    
    for interval in cheryl_busy:
        b_start, b_end = interval
        solver.add(Or(s + 60 <= b_start, s >= b_end))
    
    for interval in bradley_busy:
        b_start, b_end = interval
        solver.add(Or(s + 60 <= b_start, s >= b_end))
    
    for interval in steven_busy:
        b_start, b_end = interval
        solver.add(Or(s + 60 <= b_start, s >= b_end))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model[s].as_long()
        start_time = minutes_to_time(start_minutes)
        end_time = minutes_to_time(start_minutes + 60)
        
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()