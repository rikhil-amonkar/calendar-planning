from z3 import *

def main():
    # Create variables for day and start time (in minutes since 9:00)
    day = Int('day')
    start_time = Int('start_time')  # 0 = 9:00, 480 = 17:00

    s = Solver()

    # Define the possible days (0=Monday, 1=Tuesday, 2=Wednesday)
    s.add(day >= 0, day <= 2)
    # Start time must allow the meeting to end by 17:00 (480 minutes)
    s.add(start_time >= 0, start_time + 60 <= 480)

    # Stephanie's meetings for each day (start and end times in minutes since 9:00)
    steph_meetings = {
        0: [(30, 60), (90, 120), (150, 180), (300, 330)],  # Monday
        1: [(180, 240)],  # Tuesday (12:00-13:00)
        2: [(0, 60), (240, 300)]  # Wednesday (9:00-10:00, 13:00-14:00)
    }

    # Betty's meetings for each day
    betty_meetings = {
        0: [(0, 60), (120, 150), (330, 360), (390, 420)],  # Monday
        1: [(0, 30), (150, 180), (210, 330), (390, 420)],  # Tuesday
        2: [(60, 150), (180, 300), (330, 480)]  # Wednesday
    }

    # Add constraints for each day
    for d in range(3):
        # Constraint for Stephanie's existing meetings on day d
        for (s_start, s_end) in steph_meetings[d]:
            s.add(Implies(day == d, 
                        Not(And(start_time < s_end, start_time + 60 > s_start))))
        
        # Constraint for Betty's existing meetings on day d
        for (b_start, b_end) in betty_meetings[d]:
            s.add(Implies(day == d, 
                        Not(And(start_time < b_end, start_time + 60 > b_start))))
        
        # Betty cannot meet on Tuesday after 12:30 (210 minutes since 9:00)
        if d == 1:
            s.add(Implies(day == d, start_time + 60 <= 210))

    # Try to avoid Monday first (Stephanie's preference)
    preferred_solver = Solver()
    preferred_solver.add(s.assertions())
    preferred_solver.add(day != 0)

    if preferred_solver.check() == sat:
        model = preferred_solver.model()
    else:
        # Fallback to allowing Monday
        s.check()
        model = s.model()

    # Extract values from the model
    day_val = model[day].as_long()
    start_val = model[start_time].as_long()

    # Convert start time to HH:MM format
    hours = 9 + (start_val // 60)
    minutes = start_val % 60
    start_str = f"{hours:02d}:{minutes:02d}"

    days = ["Monday", "Tuesday", "Wednesday"]
    print(f"Schedule the meeting on {days[day_val]} at {start_str}")

if __name__ == "__main__":
    main()