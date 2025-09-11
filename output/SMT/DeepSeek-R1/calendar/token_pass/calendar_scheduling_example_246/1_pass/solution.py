from z3 import *

def main():
    # Convert time to minutes since 9:00
    def time_to_minutes(t):
        hours, minutes = map(int, t.split(':'))
        return (hours - 9) * 60 + minutes

    # Convert minutes back to HH:MM format
    def minutes_to_time(m):
        total_minutes = 9 * 60 + m
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    # Meeting duration in minutes
    meeting_duration = 30
    max_time = time_to_minutes("17:00") - meeting_duration

    # Initialize Z3 solver
    solver = Solver()
    start = Int('start')
    solver.add(start >= 0, start <= max_time)

    # Define busy intervals for each participant
    busy_intervals = [
        # Jacob
        [(time_to_minutes("13:30"), time_to_minutes("14:00")),
         (time_to_minutes("14:30"), time_to_minutes("15:00"))],
        # Diana
        [(time_to_minutes("9:30"), time_to_minutes("10:00")),
         (time_to_minutes("11:30"), time_to_minutes("12:00")),
         (time_to_minutes("13:00"), time_to_minutes("13:30")),
         (time_to_minutes("16:00"), time_to_minutes("16:30"))],
        # Adam
        [(time_to_minutes("9:30"), time_to_minutes("10:30")),
         (time_to_minutes("11:00"), time_to_minutes("12:30")),
         (time_to_minutes("15:30"), time_to_minutes("16:00"))],
        # Angela
        [(time_to_minutes("9:30"), time_to_minutes("10:00")),
         (time_to_minutes("10:30"), time_to_minutes("12:00")),
         (time_to_minutes("13:00"), time_to_minutes("15:30")),
         (time_to_minutes("16:00"), time_to_minutes("16:30"))],
        # Dennis
        [(time_to_minutes("9:00"), time_to_minutes("9:30")),
         (time_to_minutes("10:30"), time_to_minutes("11:30")),
         (time_to_minutes("13:00"), time_to_minutes("15:00")),
         (time_to_minutes("16:30"), time_to_minutes("17:00"))]
    ]

    # Add constraints for all busy intervals
    for intervals in busy_intervals:
        for b_start, b_end in intervals:
            solver.add(Or(start + meeting_duration <= b_start, start >= b_end))

    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model.evaluate(start).as_long()
        end_minutes = start_minutes + meeting_duration
        start_time = minutes_to_time(start_minutes)
        end_time = minutes_to_time(end_minutes)
        print(f"{start_time}:{end_time}")
        print("Monday")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()