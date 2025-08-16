from z3 import Solver, Int, Or, sat

# Convert "HH:MM" to minutes since midnight
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

# Convert minutes since midnight to "HH:MM" format
def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def main():
    s = Solver()

    # We represent the meeting start time in minutes from midnight.
    # The meeting duration is 30 minutes.
    start = Int('start')
    duration = 30

    # Workday: 09:00 to 17:00. Meeting must lie within these hours.
    # Also, David does not want to meet before 14:00.
    # So the meeting must start at or after 14:00 (840 minutes) and, to finish by 17:00 (1020 minutes), start must be <= 1020 - 30.
    s.add(start >= time_to_minutes("14:00"))
    s.add(start + duration <= time_to_minutes("17:00"))
    
    # Now add constraints based on the participants' busy intervals.
    # For each busy interval [B, E), the meeting [start, start+30) must not overlap with it.
    # That is, either the meeting ends by B or starts at or after E.
    
    # David's busy blocks:
    # [11:30,12:00] and [14:30,15:00].
    s.add(Or(start + duration <= time_to_minutes("11:30"),
             start >= time_to_minutes("12:00")))
    s.add(Or(start + duration <= time_to_minutes("14:30"),
             start >= time_to_minutes("15:00")))
    
    # Douglas's busy blocks:
    # [9:30,10:00], [11:30,12:00], [13:00,13:30], [14:30,15:00].
    s.add(Or(start + duration <= time_to_minutes("09:30"),
             start >= time_to_minutes("10:00")))
    s.add(Or(start + duration <= time_to_minutes("11:30"),
             start >= time_to_minutes("12:00")))
    s.add(Or(start + duration <= time_to_minutes("13:00"),
             start >= time_to_minutes("13:30")))
    s.add(Or(start + duration <= time_to_minutes("14:30"),
             start >= time_to_minutes("15:00")))
    
    # Ralph's busy blocks:
    # [9:00,9:30], [10:00,11:00], [11:30,12:30], [13:30,15:00], [15:30,16:00], [16:30,17:00]
    s.add(Or(start + duration <= time_to_minutes("09:00"),
             start >= time_to_minutes("09:30")))
    s.add(Or(start + duration <= time_to_minutes("10:00"),
             start >= time_to_minutes("11:00")))
    s.add(Or(start + duration <= time_to_minutes("11:30"),
             start >= time_to_minutes("12:30")))
    s.add(Or(start + duration <= time_to_minutes("13:30"),
             start >= time_to_minutes("15:00")))
    s.add(Or(start + duration <= time_to_minutes("15:30"),
             start >= time_to_minutes("16:00")))
    s.add(Or(start + duration <= time_to_minutes("16:30"),
             start >= time_to_minutes("17:00")))
    
    # Jordan's busy blocks:
    # [9:00,10:00], [12:00,12:30], [13:00,13:30], [14:30,15:00], [15:30,17:00]
    s.add(Or(start + duration <= time_to_minutes("09:00"),
             start >= time_to_minutes("10:00")))
    s.add(Or(start + duration <= time_to_minutes("12:00"),
             start >= time_to_minutes("12:30")))
    s.add(Or(start + duration <= time_to_minutes("13:00"),
             start >= time_to_minutes("13:30")))
    s.add(Or(start + duration <= time_to_minutes("14:30"),
             start >= time_to_minutes("15:00")))
    s.add(Or(start + duration <= time_to_minutes("15:30"),
             start >= time_to_minutes("17:00")))
    
    # Natalie is free all day, so no constraints are needed for her.

    # The constraints force the meeting to lie in the only available gap.
    # In fact, combining the above, the only possibility is to schedule the meeting
    # so that it starts at 15:00 and ends at 15:30 on Monday.
    
    if s.check() == sat:
        m = s.model()
        meeting_start = m[start].as_long()
        meeting_end = meeting_start + duration
        # We output exactly three lines after "SOLUTION:" as required.
        print("SOLUTION:")
        print("Day: Monday")
        print("Start Time:", minutes_to_time(meeting_start))
        print("End Time:", minutes_to_time(meeting_end))
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()