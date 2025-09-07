from z3 import *

def main():
    # Create a Z3 solver instance
    solver = Solver()

    # Define the meeting duration (in minutes)
    meeting_duration = 30

    # Define the meeting start time in minutes offset from 9:00.
    s = Int('s')

    # The meeting must be scheduled during work hours [9:00, 17:00].
    # In minutes from 9:00, s must be at least 0 and s+30 must be <= 480.
    solver.add(s >= 0, s + meeting_duration <= 480)

    # Busy intervals for each participant (in minutes relative to 9:00)
    # Gregory: 9:00-10:00, 10:30-11:30, 12:30-13:00, 13:30-14:00
    greg_busy = [(0, 60), (90, 150), (210, 240), (270, 300)]
    
    # Christine: 9:00-11:30, 13:30-17:00
    christine_busy = [(0, 150), (270, 480)]
    
    # Vincent: 9:00-9:30, 10:30-12:00, 12:30-14:00, 14:30-17:00
    vincent_busy = [(0, 30), (90, 180), (210, 300), (330, 480)]
    
    # Natalie: no meetings (wide open)

    # Combine all busy intervals (Natalie has no blocked time)
    busy_intervals = greg_busy + christine_busy + vincent_busy

    # For each busy interval, ensure that the meeting does not overlap.
    # Two intervals [a, a+duration) and [b, c) do not overlap if:
    # either (a+duration) <= b  or  a >= c.
    for (busy_start, busy_end) in busy_intervals:
        solver.add(Or(s + meeting_duration <= busy_start, s >= busy_end))

    # Check if the constraints are satisfiable and get a meeting start time.
    if solver.check() == sat:
        model = solver.model()
        start_val = model[s].as_long()
        end_val = start_val + meeting_duration

        # Convert the minutes offset to an actual time starting from 9:00.
        # Total minutes from midnight = 9*60 + offset.
        start_total = 9 * 60 + start_val
        end_total = 9 * 60 + end_val

        start_hour = start_total // 60
        start_minute = start_total % 60
        end_hour = end_total // 60
        end_minute = end_total % 60

        # Format the meeting time as HH:MM:HH:MM and include the day.
        meeting_time = f"{start_hour:02}:{start_minute:02}:{end_hour:02}:{end_minute:02}"
        print(f"Meeting time: {{{meeting_time}}} on Monday")
    else:
        print("No available time slot found.")

if __name__ == "__main__":
    main()