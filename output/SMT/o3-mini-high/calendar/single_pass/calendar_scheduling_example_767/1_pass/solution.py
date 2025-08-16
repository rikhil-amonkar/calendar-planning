from z3 import *

def main():
    # We represent the meeting day as an integer:
    # 0 -> Monday, 1 -> Tuesday, 2 -> Wednesday
    # The meeting start time (x) is measured in minutes from 9:00.
    # Since the workday is from 9:00 to 17:00, x must satisfy:
    # 0 <= x and x + 60 <= 480 (because meeting duration is 60 minutes)
    
    d = Int('d')
    x = Int('x')
    duration = 60
    work_start = 0      # corresponds to 9:00
    work_end = 480      # corresponds to 17:00
    
    solver = Solver()
    
    # Domain constraints
    solver.add(Or(d == 0, d == 1, d == 2))  # Only Monday, Tuesday or Wednesday
    solver.add(x >= work_start, x + duration <= work_end)
    
    # Helper: For a given busy interval [a, b] on a specific day D,
    # if the meeting is on day D, then the meeting [x, x+duration] must not overlap the busy interval.
    # This is encoded as: (x + duration <= a) or (x >= b)
    #
    # Monday constraints (d == 0):
    # Martha is busy from 16:00 to 17:00 which is [420, 480] minutes (since 16:00-9:00=7*60=420)
    solver.add(Or(d != 0, x + duration <= 420, x >= 480))
    # Beverly is busy from 9:00 to 13:30 ([0, 270]) and 14:00 to 17:00 ([300, 480])
    solver.add(Or(d != 0, x + duration <= 0, x >= 270))
    solver.add(Or(d != 0, x + duration <= 300, x >= 480))
    
    # Tuesday constraints (d == 1):
    # Martha is busy from 15:00 to 15:30: [360, 390]
    solver.add(Or(d != 1, x + duration <= 360, x >= 390))
    # Beverly is busy the entire day: [0, 480]
    solver.add(Or(d != 1, x + duration <= 0, x >= 480))
    
    # Wednesday constraints (d == 2):
    # Martha is busy from 10:00 to 11:00: [60, 120] and from 14:00 to 14:30: [300, 330]
    solver.add(Or(d != 2, x + duration <= 60, x >= 120))
    solver.add(Or(d != 2, x + duration <= 300, x >= 330))
    # Beverly is busy from 9:30 to 15:30: [30, 390] and from 16:30 to 17:00: [450, 480]
    solver.add(Or(d != 2, x + duration <= 30, x >= 390))
    solver.add(Or(d != 2, x + duration <= 450, x >= 480))
    
    if solver.check() == sat:
        model = solver.model()
        day_val = model[d].as_long()
        x_val = model[x].as_long()
        
        # Map our day integer to its name
        day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
        day_str = day_names.get(day_val, "Unknown")
        
        # Convert meeting start time (in minutes from 9:00) to HH:MM in 24-hour format.
        start_total_minutes = x_val
        start_hour = 9 + (start_total_minutes // 60)
        start_minute = start_total_minutes % 60
        
        # Compute meeting end time
        end_total_minutes = x_val + duration
        end_hour = 9 + (end_total_minutes // 60)
        end_minute = end_total_minutes % 60
        
        # Format the times with leading zeros if needed.
        start_time_formatted = f"{start_hour:02d}:{start_minute:02d}"
        end_time_formatted = f"{end_hour:02d}:{end_minute:02d}"
        
        # Print the final solution in the required format.
        output = (
            f"SOLUTION:\n"
            f"Day: {day_str}\n"
            f"Start Time: {start_time_formatted}\n"
            f"End Time: {end_time_formatted}"
        )
        print(output)
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()