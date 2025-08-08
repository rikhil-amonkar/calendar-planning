from z3 import *

def main():
    # Convert time to minutes from 9:00
    def time_to_minutes(time_str):
        h, m = time_str.split(':')
        return int(h) * 60 + int(m) - 9 * 60  # subtract 9:00 in minutes

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        total_minutes = 9 * 60 + minutes
        h = total_minutes // 60
        m = total_minutes % 60
        return f"{h:02d}:{m:02d}"

    # Define busy intervals in minutes from 9:00
    jack_busy = [
        (time_to_minutes("09:30"), time_to_minutes("10:30")),  # 30, 90
        (time_to_minutes("11:00"), time_to_minutes("11:30")),  # 120, 150
        (time_to_minutes("12:30"), time_to_minutes("13:00")),  # 210, 240
        (time_to_minutes("14:00"), time_to_minutes("14:30")),  # 300, 330
        (time_to_minutes("16:00"), time_to_minutes("16:30"))   # 420, 450
    ]
    
    charlotte_busy = [
        (time_to_minutes("09:30"), time_to_minutes("10:00")),  # 30, 60
        (time_to_minutes("10:30"), time_to_minutes("12:00")),  # 90, 180
        (time_to_minutes("12:30"), time_to_minutes("13:30")),  # 210, 270
        (time_to_minutes("14:00"), time_to_minutes("16:00"))   # 300, 420
    ]
    
    # Total work time in minutes (9:00 to 17:00 is 8 hours = 480 minutes)
    total_minutes = 480
    
    # Create Z3 solver and variable
    S = Int('S')  # Start time in minutes from 9:00
    
    # Hard constraints: work hours and non-overlapping with busy intervals
    constraints = [
        S >= 0,
        S + 30 <= total_minutes
    ]
    
    # Add constraints for Jack's busy intervals
    for (s, e) in jack_busy:
        constraints.append(Or(S + 30 <= s, S >= e))
    
    # Add constraints for Charlotte's busy intervals
    for (s, e) in charlotte_busy:
        constraints.append(Or(S + 30 <= s, S >= e))
    
    # Create solver and add hard constraints
    solver = Solver()
    solver.add(constraints)
    
    # Preference constraint: meeting ends by 12:30 (210 minutes from 9:00)
    preference = (S + 30 <= 210)
    
    # First, try with preference
    solver.push()
    solver.add(preference)
    if solver.check() == sat:
        model = solver.model()
        start_min = model[S].as_long()
    else:
        # If no solution with preference, try without
        solver.pop()
        if solver.check() == sat:
            model = solver.model()
            start_min = model[S].as_long()
        else:
            # According to the problem, a solution exists. This should not happen.
            print("No solution found")
            return
    
    # Calculate start and end times
    start_time = minutes_to_time(start_min)
    end_time = minutes_to_time(start_min + 30)
    
    # Output the solution
    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")

if __name__ == "__main__":
    main()