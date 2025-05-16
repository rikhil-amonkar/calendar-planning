from z3 import *

def find_meeting_time():
    # Create solver instance
    s = Solver()

    # Define possible days (Monday=0, Tuesday=1, Wednesday=2)
    day = Int('day')
    s.add(day >= 0, day <= 2)

    # Define start time in minutes from 9:00 (0 = 9:00, 480 = 17:00)
    start_time = Int('start_time')
    meeting_duration = 30  # 30 minutes
    s.add(start_time >= 0, start_time <= 480 - meeting_duration)

    # Define busy times for Samuel (Larry is free all week)
    samuel_busy = {
        0: [(10*60 + 30 - 9*60, 11*60 - 9*60),   # Monday 10:30-11:00
            (12*60 - 9*60, 12*60 + 30 - 9*60),    # Monday 12:00-12:30
            (13*60 - 9*60, 15*60 - 9*60),         # Monday 13:00-15:00
            (15*60 + 30 - 9*60, 16*60 + 30 - 9*60)], # Monday 15:30-16:30
        1: [(9*60 - 9*60, 12*60 - 9*60),         # Tuesday 9:00-12:00
            (14*60 - 9*60, 15*60 + 30 - 9*60),    # Tuesday 14:00-15:30
            (16*60 + 30 - 9*60, 17*60 - 9*60)],   # Tuesday 16:30-17:00
        2: [(10*60 + 30 - 9*60, 11*60 - 9*60),   # Wednesday 10:30-11:00
            (11*60 + 30 - 9*60, 12*60 - 9*60),    # Wednesday 11:30-12:00
            (12*60 + 30 - 9*60, 13*60 - 9*60),    # Wednesday 12:30-13:00
            (14*60 - 9*60, 14*60 + 30 - 9*60),    # Wednesday 14:00-14:30
            (15*60 - 9*60, 16*60 - 9*60)]         # Wednesday 15:00-16:00
    }

    # Function to check if time is available for Samuel
    def is_available(day_val, time):
        busy = samuel_busy.get(day_val, [])
        constraints = []
        for (busy_start, busy_end) in busy:
            constraints.append(Or(time >= busy_end, time + meeting_duration <= busy_start))
        return And(constraints)

    # Add constraints for Samuel
    s.add(is_available(day, start_time))

    # Larry's preference to avoid Wednesday
    s.add(day != 2)

    # Samuel's preference to avoid Tuesday
    s.add(day != 1)

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
        days = ['Monday', 'Tuesday', 'Wednesday']
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