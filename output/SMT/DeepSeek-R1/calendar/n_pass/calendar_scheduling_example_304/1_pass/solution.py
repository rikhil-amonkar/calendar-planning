from z3 import *

def main():
    # Define busy intervals in minutes from 9:00 (9:00 is 0 minutes)
    participants = {
        "Christine": [(30, 90), (180, 210), (240, 270), (330, 360), (420, 450)],
        "Janice": [],
        "Bobby": [(180, 210), (330, 360)],
        "Elizabeth": [(0, 30), (150, 240), (270, 300), (360, 390), (420, 480)],
        "Tyler": [(0, 120), (180, 210), (240, 270), (390, 420), (450, 480)],
        "Edward": [(0, 30), (60, 120), (150, 240), (330, 390), (420, 480)]
    }
    
    # Create Z3 solver and variable
    s = Int('s')
    solver = Solver()
    
    # Meeting must be within 9:00 to 17:00 and last 30 minutes
    solver.add(s >= 0)
    solver.add(s <= 450)  # 450 minutes is 16:30, so meeting ends at 17:00
    
    # Add constraints for each participant's busy intervals
    for name, intervals in participants.items():
        for interval in intervals:
            a, b = interval
            # The meeting [s, s+30) must not overlap [a, b)
            solver.add(Or(s + 30 <= a, s >= b))
    
    # First, try with Janice's preference: meeting starts before 13:00 (240 minutes from 9:00)
    solver.push()
    solver.add(s < 240)
    
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model[s].as_long()
    else:
        # If no solution with preference, try without the preference
        solver.pop()
        if solver.check() == sat:
            model = solver.model()
            start_minutes = model[s].as_long()
        else:
            # According to the problem, there is a solution, so this should not happen
            print("No solution found")
            return
    
    # Convert start_minutes back to time string
    total_minutes_start = 9 * 60 + start_minutes
    hours = total_minutes_start // 60
    minutes = total_minutes_start % 60
    start_time_str = f"{hours:02d}:{minutes:02d}"
    
    # Calculate end time (30 minutes later)
    end_minutes = start_minutes + 30
    total_minutes_end = 9 * 60 + end_minutes
    hours_end = total_minutes_end // 60
    minutes_end = total_minutes_end % 60
    end_time_str = f"{hours_end:02d}:{minutes_end:02d}"
    
    # Output the solution
    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")

if __name__ == '__main__':
    main()