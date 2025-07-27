from z3 import *

def schedule_meeting():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Define the busy intervals for Lisa and Anthony in minutes since 9:00
    lisa_busy = [
        (9 * 60, 9 * 60 + 30),    # 9:00-9:30
        (10 * 60 + 30, 11 * 60),  # 10:30-11:00
        (14 * 60, 16 * 60)        # 14:00-16:00
    ]
    
    anthony_busy = [
        (9 * 60, 9 * 60 + 30),    # 9:00-9:30
        (11 * 60, 11 * 60 + 30),  # 11:00-11:30
        (12 * 60 + 30, 13 * 60 + 30),  # 12:30-13:30
        (14 * 60, 15 * 60),        # 14:00-15:00
        (15 * 60 + 30, 16 * 60),   # 15:30-16:00
        (16 * 60 + 30, 17 * 60)   # 16:30-17:00
    ]

    # Create a Z3 solver instance
    s = Solver()

    # Define the start time of the meeting (in minutes since 9:00)
    start = Int('start')

    # Constraint: meeting must start within work hours and end before work ends
    s.add(start >= work_start)
    s.add(start + meeting_duration <= work_end)

    # Constraint: meeting does not overlap with Lisa's busy intervals
    for (busy_start, busy_end) in lisa_busy:
        s.add(Or(
            start + meeting_duration <= busy_start,
            start >= busy_end
        ))

    # Constraint: meeting does not overlap with Anthony's busy intervals
    for (busy_start, busy_end) in anthony_busy:
        s.add(Or(
            start + meeting_duration <= busy_start,
            start >= busy_end
        ))

    # Find the earliest possible start time
    s.push()
    s.check()
    m = s.model()
    earliest_start = m[start].as_long()
    s.pop()

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    start_time = minutes_to_time(earliest_start)
    end_time = minutes_to_time(earliest_start + meeting_duration)

    # Print the solution
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")

schedule_meeting()