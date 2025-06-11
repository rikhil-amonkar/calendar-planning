from z3 import *

def main():
    # Convert time string to minutes from 9:00
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return (hour - 9) * 60 + minute

    # Convert minutes back to time string
    def minutes_to_time(mins):
        total_minutes = mins
        hour = 9 + total_minutes // 60
        minute = total_minutes % 60
        return f"{hour}:{minute:02d}"

    # Busy intervals for each participant in minutes (from 9:00)
    busy_times = {
        'Gregory': [('9:00', '9:30'), ('11:30', '12:00')],
        'Jonathan': [('9:00', '9:30'), ('12:00', '12:30'), ('13:00', '13:30'), ('15:00', '16:00'), ('16:30', '17:00')],
        'Barbara': [('10:00', '10:30'), ('13:30', '14:00')],
        'Jesse': [('10:00', '11:00'), ('12:30', '14:30')],
        'Alan': [('9:30', '11:00'), ('11:30', '12:30'), ('13:00', '15:30'), ('16:00', '17:00')],
        'Nicole': [('9:00', '10:30'), ('11:30', '12:00'), ('12:30', '13:30'), ('14:00', '17:00')],
        'Catherine': [('9:00', '10:30'), ('12:00', '13:30'), ('15:00', '15:30'), ('16:00', '16:30')],
    }

    # Convert all busy times to minutes
    busy_intervals = {}
    for person, slots in busy_times.items():
        intervals = []
        for (start_str, end_str) in slots:
            s_min = time_to_minutes(start_str)
            e_min = time_to_minutes(end_str)
            intervals.append((s_min, e_min))
        busy_intervals[person] = intervals

    # Create Z3 solver and variable for meeting start time
    s = Solver()
    start = Int('start')
    meeting_duration = 30

    # Constraint: Meeting must be within 9:00 to 17:00
    s.add(start >= 0)
    s.add(start <= 450)  # 450 minutes = 16:30, so meeting ends at 17:00

    # Add constraints for each participant's busy intervals
    for person, intervals in busy_intervals.items():
        for (s_busy, e_busy) in intervals:
            # Meeting must not overlap: either ends before busy starts or starts after busy ends
            s.add(Or(start + meeting_duration <= s_busy, start >= e_busy))

    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_val = model[start].as_long()
        start_time_str = minutes_to_time(start_val)
        end_time_str = minutes_to_time(start_val + meeting_duration)
        print(f"Monday {start_time_str} to {end_time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()