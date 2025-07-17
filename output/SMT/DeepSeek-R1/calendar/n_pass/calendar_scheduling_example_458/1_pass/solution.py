from z3 import *

def main():
    # Convert time to minutes from 9:00
    def time_to_minutes(time_str):
        h, m = time_str.split(':')
        return int(h) * 60 + int(m) - 9 * 60  # Offset from 9:00

    # Busy intervals for each participant in minutes from 9:00
    busy_intervals = {
        'Melissa': [(time_to_minutes('10:00'), time_to_minutes('11:00')),
                    (time_to_minutes('12:30'), time_to_minutes('14:00')),
                    (time_to_minutes('15:00'), time_to_minutes('15:30'))],
        'Catherine': [],
        'Gregory': [(time_to_minutes('12:30'), time_to_minutes('13:00')),
                    (time_to_minutes('15:30'), time_to_minutes('16:00'))],
        'Victoria': [(time_to_minutes('09:00'), time_to_minutes('09:30')),
                     (time_to_minutes('10:30'), time_to_minutes('11:30')),
                     (time_to_minutes('13:00'), time_to_minutes('14:00')),
                     (time_to_minutes('14:30'), time_to_minutes('15:00')),
                     (time_to_minutes('15:30'), time_to_minutes('16:30'))],
        'Thomas': [(time_to_minutes('10:00'), time_to_minutes('12:00')),
                   (time_to_minutes('12:30'), time_to_minutes('13:00')),
                   (time_to_minutes('14:30'), time_to_minutes('16:00'))],
        'Jennifer': [(time_to_minutes('09:00'), time_to_minutes('09:30')),
                     (time_to_minutes('10:00'), time_to_minutes('10:30')),
                     (time_to_minutes('11:00'), time_to_minutes('13:00')),
                     (time_to_minutes('13:30'), time_to_minutes('14:30')),
                     (time_to_minutes('15:00'), time_to_minutes('15:30')),
                     (time_to_minutes('16:00'), time_to_minutes('16:30'))],
        'Wayne': []  # No meetings, but preference to avoid before 14:00
    }

    # Create solver and start time variable
    start = Int('start')
    s1 = Solver()
    s2 = Solver()

    # Basic constraints: meeting within 9:00-17:00 and duration 30 minutes
    s1.add(start >= 0)
    s1.add(start <= 450)  # 17:00 - 30 minutes = 16:30 (450 minutes from 9:00)
    s2.add(start >= 0)
    s2.add(start <= 450)

    # Wayne's preference: meeting starts at or after 14:00 (300 minutes)
    s1.add(start >= 300)

    # Add constraints for busy intervals for both solvers
    for person, intervals in busy_intervals.items():
        for (b_start, b_end) in intervals:
            s1.add(Or(start + 30 <= b_start, start >= b_end))
            s2.add(Or(start + 30 <= b_start, start >= b_end))

    # Check with Wayne's preference first
    if s1.check() == sat:
        model = s1.model()
        start_val = model[start].as_long()
    else:
        # Check without Wayne's preference
        if s2.check() == sat:
            model = s2.model()
            start_val = model[start].as_long()
        else:
            # According to the problem, a solution exists without the preference
            start_val = None

    if start_val is None:
        print("No solution found, but the problem states one exists.")
        return

    # Convert minutes back to HH:MM
    total_minutes = start_val
    hours = 9 + total_minutes // 60
    minutes = total_minutes % 60
    start_time = f"{hours:02d}:{minutes:02d}"

    end_minutes = total_minutes + 30
    end_hours = 9 + end_minutes // 60
    end_minutes = end_minutes % 60
    end_time = f"{end_hours:02d}:{end_minutes:02d}"

    # Output the solution
    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")

if __name__ == "__main__":
    main()