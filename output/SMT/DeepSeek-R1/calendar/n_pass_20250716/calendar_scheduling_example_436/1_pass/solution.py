from z3 import *

def main():
    # Meeting duration in minutes
    duration = 30
    # Work day: 9:00 (0 minutes) to 17:00 (480 minutes)
    min_start = 0
    max_start = 480 - duration  # 450 minutes (16:30)

    # Initialize Z3 solver and variable
    solver = Solver()
    start = Int('start')
    solver.add(start >= min_start, start <= max_start)

    # Busy intervals in minutes (start, end) for each participant
    busy_intervals = [
        # Patrick
        (270, 300), (330, 360),
        # Shirley
        (0, 30), (120, 150), (180, 210), (330, 360), (420, 480),
        # Jeffrey
        (0, 30), (90, 120), (150, 180), (240, 270), (420, 480),
        # Gloria
        (150, 180), (360, 390),
        # Nathan
        (0, 30), (90, 180), (300, 480),
        # Angela
        (0, 30), (60, 120), (210, 360), (390, 450),
        # David
        (0, 30), (60, 90), (120, 300), (330, 450)
    ]

    # Add constraints: meeting must not overlap with any busy interval
    for (busy_start, busy_end) in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model[start].as_long()
        
        # Convert start time to HH:MM
        total_minutes = start_minutes
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + duration
        end_hours = 9 + end_minutes // 60
        end_minutes %= 60
        end_time = f"{end_hours}:{end_minutes:02d}"
        
        # Output the result
        print("Monday")
        print(start_time)
        print(end_time)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()