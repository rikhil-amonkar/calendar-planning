from z3 import *

def main():
    # Initialize variables
    d = Int('d')  # Day: 0=Mon, 1=Tue, 2=Wed, 3=Thu
    s = Int('s')  # Start time in minutes from 9:00

    # Define busy intervals for Mary and Alexis
    Mary_busy = {
        1: [(60, 90), (390, 420)],    # Tuesday: 10:00-10:30, 15:30-16:00
        2: [(30, 60), (360, 390)],    # Wednesday: 9:30-10:00, 15:00-15:30
        3: [(0, 60), (90, 150)]       # Thursday: 9:00-10:00, 10:30-11:30
    }

    Alexis_busy = {
        0: [(0, 60), (90, 180), (210, 450)],  # Monday: 9:00-10:00, 10:30-12:00, 12:30-16:30
        1: [(0, 60), (90, 150), (180, 330), (420, 480)],  # Tuesday
        2: [(0, 120), (150, 480)],   # Wednesday
        3: [(60, 180), (300, 330), (390, 420), (450, 480)]  # Thursday
    }

    # Basic constraints
    constraints = [
        d >= 0, d <= 3,
        s >= 0, s <= 450  # Meeting must end by 17:00 (480 minutes)
    ]

    # Add constraints for Mary's busy intervals
    for day, intervals in Mary_busy.items():
        for start_busy, end_busy in intervals:
            # Meeting [s, s+30] must not overlap [start_busy, end_busy]
            non_overlap = Or(s + 30 <= start_busy, s >= end_busy)
            constraints.append(If(d == day, non_overlap, True))

    # Add constraints for Alexis's busy intervals
    for day, intervals in Alexis_busy.items():
        for start_busy, end_busy in intervals:
            non_overlap = Or(s + 30 <= start_busy, s >= end_busy)
            constraints.append(If(d == day, non_overlap, True))

    # Define cost function to minimize (earliest day and time)
    cost = d * 1000 + s

    # Solve the problem
    opt = Optimize()
    opt.add(constraints)
    opt.minimize(cost)
    
    if opt.check() == sat:
        m = opt.model()
        day_val = m[d].as_long()
        start_minutes = m[s].as_long()
        end_minutes = start_minutes + 30
        
        # Convert day index to day name
        days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
        day_str = days[day_val]
        
        # Convert start time to HH:MM
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        
        # Convert end time to HH:MM
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        # Output the result
        print(f"Day: {day_str}, Start: {start_time}, End: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()