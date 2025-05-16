from z3 import *

def find_meeting_time():
    # Create solver instance
    s = Solver()

    # Define possible days (Monday=0, Tuesday=1)
    day = Int('day')
    s.add(day >= 0, day <= 1)

    # Define start time in minutes from 9:00 (0 = 9:00, 480 = 17:00)
    start_time = Int('start_time')
    meeting_duration = 60  # 1 hour
    s.add(start_time >= 0, start_time <= 480 - meeting_duration)

    # Define busy times for Russell (in minutes from 9:00)
    russell_busy = {
        0: [(10*60 + 30 - 9*60, 11*60 - 9*60)],  # Monday 10:30-11:00
        1: [(13*60 - 9*60, 13*60 + 30 - 9*60)]   # Tuesday 13:00-13:30
    }

    # Define busy times for Alexander (in minutes from 9:00)
    alexander_busy = {
        0: [(9*60 - 9*60, 11*60 + 30 - 9*60),    # Monday 9:00-11:30
            (12*60 - 9*60, 14*60 + 30 - 9*60),   # Monday 12:00-14:30
            (15*60 - 9*60, 17*60 - 9*60)],       # Monday 15:00-17:00
        1: [(9*60 - 9*60, 10*60 - 9*60),        # Tuesday 9:00-10:00
            (13*60 - 9*60, 14*60 - 9*60),       # Tuesday 13:00-14:00
            (15*60 - 9*60, 15*60 + 30 - 9*60),  # Tuesday 15:00-15:30
            (16*60 - 9*60, 16*60 + 30 - 9*60)]  # Tuesday 16:00-16:30
    }

    # Function to check if time is available for a person
    def is_available(person_busy, day_val, time):
        if day_val not in person_busy:
            return True  # No meetings scheduled that day
        constraints = []
        for (busy_start, busy_end) in person_busy[day_val]:
            constraints.append(Or(time >= busy_end, time + meeting_duration <= busy_start))
        return And(constraints)

    # Add constraints for both participants
    s.add(is_available(russell_busy, day, start_time))
    s.add(is_available(alexander_busy, day, start_time))

    # Russell prefers not to meet on Tuesday before 13:30
    s.add(Implies(day == 1, start_time >= (13*60 + 30 - 9*60)))

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
        days = ['Monday', 'Tuesday']
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