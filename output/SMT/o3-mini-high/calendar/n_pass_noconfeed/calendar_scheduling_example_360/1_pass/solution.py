from z3 import Solver, Int, Or, sat

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def main():
    meeting_duration = 30  # meeting duration in minutes
    meeting_start = Int('meeting_start')
    meeting_end = meeting_start + meeting_duration

    # Work hours on Monday: 9:00 (540 minutes) to 17:00 (1020 minutes)
    solver = Solver()
    solver.add(meeting_start >= 540)
    solver.add(meeting_end <= 1020)
    
    # Reservations for each participant are represented as intervals [start, end) in minutes.
    reservations = [
        # Emily's meetings: 10:00-10:30, 16:00-16:30
        (600, 630), (960, 990),
        # Maria's meetings: 10:30-11:00, 14:00-14:30
        (630, 660), (840, 870),
        # Carl's meetings: 9:30-10:00, 10:30-12:30, 13:30-14:00, 14:30-15:30, 16:00-17:00
        (570, 600), (630, 750), (810, 840), (870, 930), (960, 1020),
        # David's meetings: 9:30-11:00, 11:30-12:00, 12:30-13:30, 14:00-15:00, 16:00-17:00
        (570, 660), (690, 720), (750, 810), (840, 900), (960, 1020),
        # Frank's meetings: 9:30-10:30, 11:00-11:30, 12:30-13:30, 14:30-17:00
        (570, 630), (660, 690), (750, 810), (870, 1020)
        # Mason is free all day.
    ]

    # For the meeting to not conflict with a reservation, it must either end by the start
    # of the reservation or start after the reservation ends.
    for res_start, res_end in reservations:
        solver.add(Or(meeting_end <= res_start, meeting_start >= res_end))
    
    if solver.check() == sat:
        model = solver.model()
        start_val = model[meeting_start].as_long()
        end_val = start_val + meeting_duration
        
        # Convert minutes back to HH:MM format
        start_time = minutes_to_time(start_val)
        end_time = minutes_to_time(end_val)
        day = "Monday"
        
        # Output in the format: "Monday HH:MM:HH:MM"
        print(f"{day} {start_time}:{end_time}")
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()