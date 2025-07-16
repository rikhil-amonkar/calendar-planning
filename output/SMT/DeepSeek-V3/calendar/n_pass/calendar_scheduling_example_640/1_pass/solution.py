from z3 import *

def solve_scheduling():
    # Create a solver instance
    s = Solver()

    # Define the possible days
    days = ['Monday', 'Tuesday']
    day = Int('day')
    s.add(day >= 0, day <= 1)  # 0 for Monday, 1 for Tuesday

    # Define the start time in minutes from 9:00 (540 minutes)
    start_time = Int('start_time')
    s.add(start_time >= 540, start_time <= 1020 - 30)  # 17:00 is 1020 minutes, meeting is 30 mins

    # Extract busy intervals for Bobby and Michael on each day
    bobby_busy = {
        'Monday': [(14*60 + 30, 15*60)],  # 14:30-15:00
        'Tuesday': [(9*60, 11*60 + 30), (12*60, 12*60 + 30), (13*60, 15*60), (15*60 + 30, 17*60)]
    }
    michael_busy = {
        'Monday': [(9*60, 10*60), (10*60 + 30, 13*60 + 30), (14*60, 15*60), (15*60 + 30, 17*60)],
        'Tuesday': [(9*60, 10*60 + 30), (11*60, 11*60 + 30), (12*60, 14*60), (15*60, 16*60), (16*60 + 30, 17*60)]
    }

    # Function to check if a time slot is free for a person on a given day
    def is_free(person_busy, day_idx, start, duration):
        day_name = days[day_idx]
        intervals = person_busy[day_name]
        # The meeting is from start to start + duration
        meeting_start = start
        meeting_end = start + duration
        # Check that the meeting does not overlap with any busy interval
        return And([Or(meeting_end <= busy_start, meeting_start >= busy_end) 
                    for (busy_start, busy_end) in intervals])

    # Duration is 30 minutes
    duration = 30

    # Both Bobby and Michael must be free during the meeting time
    s.add(is_free(bobby_busy, day, start_time, duration))
    s.add(is_free(michael_busy, day, start_time, duration))

    # To find the earliest time, we minimize the day and then the start time
    # We'll use a lexicographic order: first day, then start_time
    opt = Optimize()
    opt.add(s.assertions())
    opt.minimize(day)
    opt.minimize(start_time)

    if opt.check() == sat:
        m = opt.model()
        day_idx = m[day].as_long()
        start_min = m[start_time].as_long()
        day_name = days[day_idx]
        start_hour = start_min // 60
        start_minute = start_min % 60
        end_min = start_min + duration
        end_hour = end_min // 60
        end_minute = end_min % 60
        print(f"SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
        print(f"End Time: {end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

solve_scheduling()