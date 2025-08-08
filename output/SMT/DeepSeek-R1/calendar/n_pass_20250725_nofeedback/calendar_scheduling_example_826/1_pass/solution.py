from z3 import *

def main():
    # Define variables
    D = Int('D')
    T = Int('T')
    S = D * (24 * 60) + T  # absolute start time in minutes from Monday 00:00

    # Constraints list
    constraints = [
        Or(D == 0, D == 1, D == 2, D == 3),  # Day must be Mon, Tue, Wed, or Thu
        T >= 540,  # 9:00 in minutes
        T <= 990   # 16:30 in minutes (since meeting ends at 17:00)
    ]

    # Busy intervals for James per day (start, end) in minutes of the day (half-open intervals [start, end))
    busy = {
        0: [(540, 570), (630, 660), (750, 780), (870, 930), (990, 1020)],  # Monday
        1: [(540, 660), (690, 720), (750, 930), (960, 1020)],  # Tuesday
        2: [(600, 660), (720, 780), (810, 960)],  # Wednesday
        3: [(570, 690), (720, 750), (780, 810), (840, 870), (990, 1020)]   # Thursday
    }

    # For each day, add constraints to avoid overlapping with busy intervals
    for day, intervals in busy.items():
        day_constraints = []
        for start, end in intervals:
            # Meeting [T, T+30) must not overlap with [start, end): either ends before start or starts after end
            day_constraints.append(Or(T + 30 <= start, T >= end))
        # If D is this day, apply the constraints for all intervals
        constraints.append(If(D == day, And(day_constraints), True))

    # Use Optimize to minimize S (earliest time)
    opt = Optimize()
    opt.add(constraints)
    opt.minimize(S)

    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        d_val = m.eval(D).as_long()
        t_val = m.eval(T).as_long()
        days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
        day_str = days[d_val]
        # Format start time (HH:MM)
        start_hour = t_val // 60
        start_minute = t_val % 60
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        # Calculate end time (start time + 30 minutes)
        end_minutes = t_val + 30
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        # Output the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()