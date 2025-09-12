from z3 import *

def main():
    # Initialize variables
    s = Int('s')  # Start time in minutes from 9:00
    d = Int('d')  # Day: 0=Monday, 1=Tuesday, 2=Wednesday

    # Initialize solver
    solver = Solver()

    # Define constraints for day and start time
    solver.add(d >= 0, d <= 2)
    solver.add(s >= 0, s <= 450)  # 480 minutes (8 hours) - 30 minutes

    # Joshua's busy intervals (minutes from 9:00)
    joshua_monday = [(360, 390)]  # 15:00-15:30
    joshua_tuesday = [(150, 180), (240, 270), (330, 360)]  # 11:30-12:00, 13:00-13:30, 14:30-15:00
    joshua_wednesday = []

    # Joyce's busy intervals (minutes from 9:00)
    joyce_monday = [(0, 30), (60, 120), (150, 210), (240, 360), (390, 480)]  # 9:00-9:30, 10:00-11:00, 11:30-12:30, 13:00-15:00, 15:30-17:00
    joyce_tuesday = [(0, 480)]  # 9:00-17:00 (entire day)
    joyce_wednesday = [(0, 30), (60, 120), (210, 390), (420, 450)]  # 9:00-9:30, 10:00-11:00, 12:30-15:30, 16:00-16:30

    # Add constraints for Joshua's schedules
    for start, end in joshua_monday:
        solver.add(Implies(d == 0, Or(s + 30 <= start, s >= end)))
    for start, end in joshua_tuesday:
        solver.add(Implies(d == 1, Or(s + 30 <= start, s >= end)))
    for start, end in joshua_wednesday:
        solver.add(Implies(d == 2, Or(s + 30 <= start, s >= end)))

    # Add constraints for Joyce's schedules
    for start, end in joyce_monday:
        solver.add(Implies(d == 0, Or(s + 30 <= start, s >= end)))
    for start, end in joyce_tuesday:
        solver.add(Implies(d == 1, Or(s + 30 <= start, s >= end)))
    for start, end in joyce_wednesday:
        solver.add(Implies(d == 2, Or(s + 30 <= start, s >= end)))

    # Joyce's preference: Not on Monday before 12:00 (180 minutes from 9:00)
    solver.add(Implies(d == 0, s >= 180))

    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        day_val = model[d].as_long()
        start_val = model[s].as_long()
        
        # Convert day value to string
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[day_val]
        
        # Calculate start and end times
        start_hour = 9 + start_val // 60
        start_minute = start_val % 60
        end_val = start_val + 30
        end_hour = 9 + end_val // 60
        end_minute = end_val % 60
        
        # Format output
        print(f"{day_str} {start_hour}:{start_minute:02d}:{end_hour}:{end_minute:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()