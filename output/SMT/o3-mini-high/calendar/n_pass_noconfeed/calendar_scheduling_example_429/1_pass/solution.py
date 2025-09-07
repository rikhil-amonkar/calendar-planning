from z3 import *

def main():
    # Meeting duration in minutes
    duration = 30
    # Working hours on Monday: 9:00 to 17:00.
    # We use a relative time such that 9:00 is 0 minutes and 17:00 is 480 minutes.
    # Because the meeting must finish by 480 minutes, the meeting start s must satisfy s + duration <= 480.
    earliest = 0
    latest = 480 - duration   # 450

    # The meeting start time (in minutes after 9:00)
    s = Int('s')
    
    solver = Solver()
    solver.add(s >= earliest, s <= latest)
    
    # Define the busy intervals for each person in minutes relative to 9:00.
    # The meeting interval [s, s+duration] must NOT overlap any of these intervals.
    busy_intervals = [
        # Judy
        (240, 270),  # 13:00 to 13:30
        (420, 450),  # 16:00 to 16:30
        # Olivia
        (60, 90),    # 10:00 to 10:30
        (180, 240),  # 12:00 to 13:00
        (300, 330),  # 14:00 to 14:30
        # Jacqueline
        (60, 90),    # 10:00 to 10:30
        (360, 390),  # 15:00 to 15:30
        # Laura
        (0, 60),     # 9:00 to 10:00
        (90, 180),   # 10:30 to 12:00
        (240, 270),  # 13:00 to 13:30
        (330, 360),  # 14:30 to 15:00
        (390, 480),  # 15:30 to 17:00
        # Tyler
        (0, 60),     # 9:00 to 10:00
        (120, 150),  # 11:00 to 11:30
        (210, 240),  # 12:30 to 13:00
        (300, 330),  # 14:00 to 14:30
        (390, 480),  # 15:30 to 17:00
        # Lisa
        (30, 90),    # 9:30 to 10:30
        (120, 150),  # 11:00 to 11:30
        (180, 210),  # 12:00 to 12:30
        (240, 270),  # 13:00 to 13:30
        (300, 330),  # 14:00 to 14:30
        (420, 480)   # 16:00 to 17:00
    ]
    
    # For each busy interval [b_start, b_end], add the constraint that
    # the meeting [s, s+duration] does not overlap it.
    # That is, either the meeting finishes by b_start (s+duration <= b_start)
    # or the meeting starts at or after b_end (s >= b_end).
    for b_start, b_end in busy_intervals:
        solver.add(Or(s + duration <= b_start, s >= b_end))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        meeting_start_rel = model[s].as_long()  # meeting start time in minutes relative to 9:00
        meeting_end_rel = meeting_start_rel + duration
        
        # Convert relative times to absolute times.
        # 9:00 is 9*60 = 540 minutes from midnight.
        meeting_start_abs = 9 * 60 + meeting_start_rel
        meeting_end_abs = 9 * 60 + meeting_end_rel
        
        # Convert minutes to HH:MM format.
        start_hour = meeting_start_abs // 60
        start_min = meeting_start_abs % 60
        end_hour = meeting_end_abs // 60
        end_min = meeting_end_abs % 60
        
        # Format the output as HH:MM:HH:MM and print the day
        time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
        print("Monday")
        print(time_str)
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()