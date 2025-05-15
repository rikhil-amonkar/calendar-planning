from z3 import *

def find_meeting_time():
    # Create solver instance
    s = Solver()

    # Define possible days (Monday=0, Tuesday=1, Wednesday=2, Thursday=3)
    day = Int('day')
    s.add(day >= 0, day <= 3)

    # Define start time in minutes from 9:00 (0 = 9:00, 480 = 17:00)
    start_time = Int('start_time')
    meeting_duration = 30  # 30 minutes
    s.add(start_time >= 0, start_time <= 480 - meeting_duration)

    # Define busy times for James (Cheryl is free all week)
    james_busy = {
        0: [(9*60 - 9*60, 9*60 + 30 - 9*60),    # Monday 9:00-9:30
            (10*60 + 30 - 9*60, 11*60 - 9*60),   # Monday 10:30-11:00
            (12*60 + 30 - 9*60, 13*60 - 9*60),   # Monday 12:30-13:00
            (14*60 + 30 - 9*60, 15*60 + 30 - 9*60), # Monday 14:30-15:30
            (16*60 + 30 - 9*60, 17*60 - 9*60)],  # Monday 16:30-17:00
        1: [(9*60 - 9*60, 11*60 - 9*60),        # Tuesday 9:00-11:00
            (11*60 + 30 - 9*60, 12*60 - 9*60),   # Tuesday 11:30-12:00
            (12*60 + 30 - 9*60, 15*60 + 30 - 9*60), # Tuesday 12:30-15:30
            (16*60 - 9*60, 17*60 - 9*60)],       # Tuesday 16:00-17:00
        2: [(10*60 - 9*60, 11*60 - 9*60),       # Wednesday 10:00-11:00
            (12*60 - 9*60, 13*60 - 9*60),       # Wednesday 12:00-13:00
            (13*60 + 30 - 9*60, 16*60 - 9*60)], # Wednesday 13:30-16:00
        3: [(9*60 + 30 - 9*60, 11*60 + 30 - 9*60), # Thursday 9:30-11:30
            (12*60 - 9*60, 12*60 + 30 - 9*60),   # Thursday 12:00-12:30
            (13*60 - 9*60, 13*60 + 30 - 9*60),   # Thursday 13:00-13:30
            (14*60 - 9*60, 14*60 + 30 - 9*60),   # Thursday 14:00-14:30
            (16*60 + 30 - 9*60, 17*60 - 9*60)]   # Thursday 16:30-17:00
    }

    # Function to check if time is available for James
    def is_available(day_val, time):
        busy = james_busy.get(day_val, [])
        constraints = []
        for (busy_start, busy_end) in busy:
            constraints.append(Or(time >= busy_end, time + meeting_duration <= busy_start))
        return And(constraints)

    # Add constraints for James
    s.add(is_available(day, start_time))

    # Cheryl's preferences to avoid Wednesday and Thursday
    s.add(Or(day == 0, day == 1))  # Only Monday or Tuesday

    # To find the earliest time, we'll minimize (day*1000 + start_time)
    objective = day * 1000 + start_time
    opt = Optimize()
    opt.add(s.assertions())
    opt.minimize(objective)

    # Check if a solution exists
    if opt.check() == sat:
        model = opt.model()
        day_val = model[day].as_long()
        start = model[start_time].as_long()
        
        # Convert to human-readable format
        days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
        start_hour = start // 60 + 9
        start_minute = start % 60
        end = start + meeting_duration
        end_hour = end // 60 + 9
        end_minute = end % 60
        
        return {
            'day': days[day_val],
            'start_time': f"{start_hour:02d}:{start_minute:02d}",
            'end_time': f"{end_hour:02d}:{end_minute:02d}"
        }
    else:
        return None

# Find and print the meeting time
meeting_time = find_meeting_time()
if meeting_time:
    print(f"Meeting scheduled on {meeting_time['day']} from {meeting_time['start_time']} to {meeting_time['end_time']}")
else:
    print("No valid meeting time found.")