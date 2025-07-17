from z3 import *

def main():
    # Convert time to minutes from 9:00 (9:00 is 0)
    # Participants' busy intervals in minutes
    intervals = {
        "Christine": [(30, 90), (180, 210), (240, 270), (330, 360), (420, 450)],
        "Janice": [],
        "Bobby": [(180, 210), (330, 360)],
        "Elizabeth": [(0, 30), (150, 240), (270, 300), (360, 390), (420, 480)],
        "Tyler": [(0, 120), (180, 210), (240, 270), (390, 420), (450, 480)],
        "Edward": [(0, 30), (60, 120), (150, 300), (330, 390), (420, 480)]
    }
    
    # First, try with Janice's preference: meeting ends by 13:00 (240 minutes) -> S <= 210
    S = Int('S')
    solver = Solver()
    solver.add(S >= 0)
    solver.add(S <= 210)  # so that meeting ends by 13:00 (240 minutes)
    
    # Add constraints for each participant's busy intervals
    for person, busy_list in intervals.items():
        for (start, end) in busy_list:
            # The meeting [S, S+30) should not overlap [start, end)
            solver.add(Or(S + 30 <= start, S >= end))
    
    if solver.check() == sat:
        m = solver.model()
        start_minutes = m[S].as_long()
    else:
        # If no solution with preference, try without the preference (meeting any time during work hours)
        solver2 = Solver()
        S2 = Int('S2')
        solver2.add(S2 >= 0)
        solver2.add(S2 <= 450)  # meeting must end by 17:00 (480 minutes)
        for person, busy_list in intervals.items():
            for (start, end) in busy_list:
                solver2.add(Or(S2 + 30 <= start, S2 >= end))
        if solver2.check() == sat:
            m = solver2.model()
            start_minutes = m[S2].as_long()
        else:
            print("No solution found")
            return
    
    # Convert minutes back to time string
    total_minutes = start_minutes
    hours = 9 + total_minutes // 60
    minutes = total_minutes % 60
    start_time = f"{hours}:{minutes:02d}"
    
    total_minutes_end = start_minutes + 30
    hours_end = 9 + total_minutes_end // 60
    minutes_end = total_minutes_end % 60
    end_time = f"{hours_end}:{minutes_end:02d}"
    
    print(f"Monday {start_time} to {end_time}")

if __name__ == "__main__":
    main()