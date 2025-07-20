from z3 import Int, Or, And, Solver, sat

# Convert time string to minutes past 9:00
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return (hours - 9) * 60 + minutes

# Convert minutes back to time string
def minutes_to_time(minutes):
    total_minutes = minutes
    hours = 9 + total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def main():
    # Meeting duration in minutes
    duration = 60
    
    # Define busy intervals for each participant (converted to minutes past 9:00)
    stephanie_busy = [(time_to_minutes("10:00"), time_to_minutes("10:30")),
                      (time_to_minutes("16:00"), time_to_minutes("16:30"))]
    
    cheryl_busy = [(time_to_minutes("10:00"), time_to_minutes("10:30")),
                   (time_to_minutes("11:30"), time_to_minutes("12:00")),
                   (time_to_minutes("13:30"), time_to_minutes("14:00")),
                   (time_to_minutes("16:30"), time_to_minutes("17:00"))]
    
    bradley_busy = [(time_to_minutes("9:30"), time_to_minutes("10:00")),
                    (time_to_minutes("10:30"), time_to_minutes("11:30")),
                    (time_to_minutes("13:30"), time_to_minutes("14:00")),
                    (time_to_minutes("14:30"), time_to_minutes("15:00")),
                    (time_to_minutes("15:30"), time_to_minutes("17:00"))]
    
    steven_busy = [(time_to_minutes("9:00"), time_to_minutes("12:00")),
                   (time_to_minutes("13:00"), time_to_minutes("13:30")),
                   (time_to_minutes("14:30"), time_to_minutes("17:00"))]
    
    # Z3 variables and solver
    s = Int('start_time')
    solver = Solver()
    
    # Global constraints: meeting within 9:00-17:00
    solver.add(s >= 0)                     # Start at or after 9:00
    solver.add(s + duration <= 8 * 60)     # End at or before 17:00 (480 minutes)
    
    # Avoid busy intervals for each participant
    def add_busy_constraints(busy_intervals):
        for start, end in busy_intervals:
            # Meeting must be entirely before or after each busy interval
            solver.add(Or(s + duration <= start, s >= end))
    
    add_busy_constraints(stephanie_busy)
    add_busy_constraints(cheryl_busy)
    add_busy_constraints(bradley_busy)
    add_busy_constraints(steven_busy)
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model[s].as_long()
        end_minutes = start_minutes + duration
        
        # Convert to time strings
        start_time = minutes_to_time(start_minutes)
        end_time = minutes_to_time(end_minutes)
        
        print(f"Monday {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()