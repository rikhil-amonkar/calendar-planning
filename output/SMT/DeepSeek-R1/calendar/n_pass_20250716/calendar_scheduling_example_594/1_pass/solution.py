from z3 import *

def main():
    # Convert time to minutes from 9:00
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return (hours - 9) * 60 + minutes

    # Busy periods for Adam and Roy
    adam_busy = [
        ("9:30", "10:00"),
        ("12:30", "13:00"),
        ("14:30", "15:00"),
        ("16:30", "17:00")
    ]
    roy_busy = [
        ("10:00", "11:00"),
        ("11:30", "13:00"),
        ("13:30", "14:30"),
        ("16:30", "17:00")
    ]

    # Convert busy periods to minutes
    adam_busy_min = [(time_to_minutes(start), time_to_minutes(end)) for start, end in adam_busy]
    roy_busy_min = [(time_to_minutes(start), time_to_minutes(end)) for start, end in roy_busy]

    # Total work duration in minutes (9:00 to 17:00 is 8 hours)
    total_minutes = 8 * 60

    # Create solver and variables
    s = Optimize()
    start = Int('start')

    # Constraints: within work hours
    s.add(start >= 0)
    s.add(start + 30 <= total_minutes)  # Meeting end time

    # Add constraints for each busy period
    for (busy_start, busy_end) in adam_busy_min:
        s.add(Or(start + 30 <= busy_start, start >= busy_end))
    for (busy_start, busy_end) in roy_busy_min:
        s.add(Or(start + 30 <= busy_start, start >= busy_end))

    # Minimize start time to find earliest slot
    s.minimize(start)

    # Check and get solution
    if s.check() == sat:
        m = s.model()
        start_val = m[start].as_long()
        # Convert minutes back to time string
        hours = 9 + start_val // 60
        minutes = start_val % 60
        end_val = start_val + 30
        end_hours = 9 + end_val // 60
        end_minutes = end_val % 60
        print(f"Monday {hours:02d}:{minutes:02d} to {end_hours:02d}:{end_minutes:02d}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()