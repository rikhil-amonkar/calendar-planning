from z3 import *

def main():
    # Convert time to minutes from 00:00
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 30  # minutes

    # Busy intervals for each participant in minutes
    bradley_busy = [
        ("9:30", "10:00"),
        ("12:30", "13:00"),
        ("13:30", "14:00"),
        ("15:30", "16:00")
    ]
    teresa_busy = [
        ("10:30", "11:00"),
        ("12:00", "12:30"),
        ("13:00", "13:30"),
        ("14:30", "15:00")
    ]
    elizabeth_busy = [
        ("9:00", "9:30"),
        ("10:30", "11:30"),
        ("13:00", "13:30"),
        ("14:30", "15:00"),
        ("15:30", "17:00")
    ]
    christian_busy = [
        ("9:00", "9:30"),
        ("10:30", "17:00")
    ]

    # Convert all busy times to minutes
    def convert_intervals(intervals):
        return [(time_to_minutes(start), time_to_minutes(end)) for start, end in intervals]

    bradley_intervals = convert_intervals(bradley_busy)
    teresa_intervals = convert_intervals(teresa_busy)
    elizabeth_intervals = convert_intervals(elizabeth_busy)
    christian_intervals = convert_intervals(christian_busy)

    # Z3 solver
    solver = Solver()
    start = Int('start')

    # Constraint: Meeting must be within work hours
    solver.add(start >= work_start)
    solver.add(start + meeting_duration <= work_end)

    # Function to add no-overlap constraints for a set of intervals
    def add_no_overlap(intervals):
        for busystart, busyend in intervals:
            solver.add(Or(start + meeting_duration <= busystart, start >= busyend))

    add_no_overlap(bradley_intervals)
    add_no_overlap(teresa_intervals)
    add_no_overlap(elizabeth_intervals)
    add_no_overlap(christian_intervals)

    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_val = model.eval(start).as_long()
        end_val = start_val + meeting_duration
        start_time = minutes_to_time(start_val)
        end_time = minutes_to_time(end_val)
        print(f"{start_time}:{end_time}")
        print("Monday")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()