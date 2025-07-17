from z3 import *

def main():
    # Create variables
    d = Int('d')  # day: 0=Monday, 1=Tuesday, 2=Wednesday
    s = Int('s')  # start time in minutes from 9:00

    # Constraints list
    constraints = []

    # Day must be 0, 1, or 2
    constraints.append(d >= 0)
    constraints.append(d <= 2)

    # Start time must be between 0 (9:00) and 450 (16:30) inclusive, because meeting ends by 17:00 (480 minutes from 9:00)
    constraints.append(s >= 0)
    constraints.append(s <= 450)

    # Define busy periods as half-open intervals [start, end)
    amy_busy = {
        0: [],  # Monday
        1: [],  # Tuesday
        2: [(120, 150), (270, 300)]  # Wednesday: 11:00-11:30, 13:30-14:00
    }

    pamela_busy = {
        0: [(0, 90), (120, 450)],  # Monday: 9:00-10:30, 11:00-16:30
        1: [(0, 30), (60, 480)],   # Tuesday: 9:00-9:30, 10:00-17:00
        2: [(0, 30), (60, 120), (150, 270), (330, 360), (420, 450)]  # Wednesday: various periods
    }

    # Function to avoid overlapping with busy intervals
    def avoid_busy_intervals(participant_busy):
        list_constraints = []
        for day, intervals in participant_busy.items():
            for (b_start, b_end) in intervals:
                # If the meeting day is `day`, then ensure no overlap with [b_start, b_end)
                c = Implies(d == day, Or(s >= b_end, s + 30 <= b_start))
                list_constraints.append(c)
        return list_constraints

    # Add constraints for Amy and Pamela
    constraints.extend(avoid_busy_intervals(amy_busy))
    constraints.extend(avoid_busy_intervals(pamela_busy))

    # Define penalty for preferences
    penalty = Int('penalty')
    # Penalty: 100 for Monday, 50 for Wednesday before 16:00 (16:00 is 420 minutes from 9:00), 0 otherwise
    penalty_def = If(d == 0, 100, If(And(d == 2, s < 420), 50, 0))
    constraints.append(penalty == penalty_def)

    # Use Optimize to minimize penalty
    opt = Optimize()
    opt.add(constraints)
    opt.minimize(penalty)

    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        day_val = m[d].as_long()
        s_val = m[s].as_long()
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[day_val]
        
        # Calculate start time (HH:MM)
        total_minutes = s_val
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_hour = 9 + hours
        start_min = minutes
        start_time = f"{start_hour:02d}:{minutes:02d}"
        
        # Calculate end time (start time + 30 minutes)
        end_minutes = s_val + 30
        hours_end = end_minutes // 60
        minutes_end = end_minutes % 60
        end_hour = 9 + hours_end
        end_time = f"{end_hour:02d}:{minutes_end:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()