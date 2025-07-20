from z3 import Solver, Int, Or, And

def main():
    # Initialize Z3 solver and variable
    s = Solver()
    start_min = Int('start_min')

    # Total available time: 9:00 (0 min) to 17:00 (480 min)
    # Meeting duration: 30 minutes, so start must be between 0 and 450 minutes
    s.add(start_min >= 0)
    s.add(start_min <= 450)  # 480 - 30 = 450

    # Define busy intervals in minutes for each participant (relative to 9:00)
    john_busy = [(150, 180), (300, 330)]
    megan_busy = [(180, 210), (300, 360), (390, 420)]
    brandon_busy = []  # No meetings
    kimberly_busy = [(0, 30), (60, 90), (120, 330), (360, 420), (450, 480)]
    sean_busy = [(60, 120), (150, 300), (360, 390)]
    lori_busy = [(0, 30), (90, 180), (240, 330), (420, 450)]

    # Combine all participants' busy intervals
    all_busy = [john_busy, megan_busy, brandon_busy, kimberly_busy, sean_busy, lori_busy]

    # Add constraints for each participant
    for participant in all_busy:
        for (busy_start, busy_end) in participant:
            # Ensure meeting does not overlap with busy interval
            s.add(Or(
                start_min + 30 <= busy_start,
                start_min >= busy_end
            ))

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        start_val = model[start_min].as_long()
        # Convert minutes back to time string
        total_minutes = start_val
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours}:{minutes:02d}"
        end_minutes = total_minutes + 30
        end_hours = 9 + end_minutes // 60
        end_min = end_minutes % 60
        end_time = f"{end_hours}:{end_min:02d}"
        print(f"Monday {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()