from z3 import Int, Solver, Or, sat

def minutes_to_hhmm(m):
    # m is minutes after 9:00. Compute absolute time from 9:00.
    total_minutes = 9 * 60 + m
    hour = total_minutes // 60
    minute = total_minutes % 60
    return f"{hour:02d}:{minute:02d}"

def main():
    duration = 30  # meeting duration is 30 minutes

    # Define s: meeting start time in minutes after 9:00.
    s = Int('s')
    solver = Solver()
    
    # Constraint: meeting must start between 9:00 and 16:30 so that it ends by 17:00.
    solver.add(s >= 0, s <= 450)
    
    # Busy intervals for each participant (in minutes after 9:00):
    busy_intervals = [
        # Cynthia's busy intervals:
        (0, 30),    # 9:00 - 9:30
        (60, 90),   # 10:00 - 10:30
        (270, 330), # 13:30 - 14:30
        (360, 420), # 15:00 - 16:00

        # Ann's busy intervals:
        (60, 120),  # 10:00 - 11:00
        (240, 270), # 13:00 - 13:30
        (300, 360), # 14:00 - 15:00
        (420, 450), # 16:00 - 16:30

        # Catherine's busy intervals:
        (0, 150),   # 9:00 - 11:30
        (210, 270), # 12:30 - 13:30
        (330, 480), # 14:30 - 17:00

        # Kyle's busy intervals:
        (0, 30),    # 9:00 - 9:30
        (60, 150),  # 10:00 - 11:30
        (180, 210), # 12:00 - 12:30
        (240, 330), # 13:00 - 14:30
        (360, 420)  # 15:00 - 16:00
    ]
    
    # For each busy interval, ensure the meeting [s, s+duration) does not overlap.
    # That is, for a busy interval [b_start, b_end), we require:
    # either the meeting finishes by b_start (s + duration <= b_start)
    # or starts after the busy period (s >= b_end).
    for b_start, b_end in busy_intervals:
        solver.add(Or(s + duration <= b_start, s >= b_end))
    
    # Solve for a valid meeting start time.
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[s].as_long()
        meeting_end = meeting_start + duration
        
        start_time_str = minutes_to_hhmm(meeting_start)
        end_time_str = minutes_to_hhmm(meeting_end)
        
        # Print the solution in the required format.
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found.")
        
if __name__ == '__main__':
    main()