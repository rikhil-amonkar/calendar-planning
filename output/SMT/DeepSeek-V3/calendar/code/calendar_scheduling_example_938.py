from z3 import *

def find_meeting_time():
    # Create solver instance
    s = Solver()

    # Define possible days (Monday=0, Tuesday=1, Wednesday=2, Thursday=3, Friday=4)
    day = Int('day')
    s.add(day >= 0, day <= 4)

    # Define start time in minutes from 9:00 (0 = 9:00, 480 = 17:00)
    start_time = Int('start_time')
    meeting_duration = 30  # 30 minutes
    s.add(start_time >= 0, start_time <= 480 - meeting_duration)

    # Define busy times for Eugene (in minutes from 9:00)
    eugene_busy = {
        0: [(11*60 - 9*60, 12*60 - 9*60),       # Monday 11:00-12:00
            (13*60 + 30 - 9*60, 14*60 - 9*60),  # Monday 13:30-14:00
            (14*60 + 30 - 9*60, 15*60 - 9*60),  # Monday 14:30-15:00
            (16*60 - 9*60, 16*60 + 30 - 9*60)], # Monday 16:00-16:30
        2: [(9*60 - 9*60, 9*60 + 30 - 9*60),    # Wednesday 9:00-9:30
            (11*60 - 9*60, 11*60 + 30 - 9*60),  # Wednesday 11:00-11:30
            (12*60 - 9*60, 12*60 + 30 - 9*60),  # Wednesday 12:00-12:30
            (13*60 + 30 - 9*60, 15*60 - 9*60)], # Wednesday 13:30-15:00
        3: [(9*60 + 30 - 9*60, 10*60 - 9*60),   # Thursday 9:30-10:00
            (11*60 - 9*60, 12*60 + 30 - 9*60)], # Thursday 11:00-12:30
        4: [(10*60 + 30 - 9*60, 11*60 - 9*60),  # Friday 10:30-11:00
            (12*60 - 9*60, 12*60 + 30 - 9*60),  # Friday 12:00-12:30
            (13*60 - 9*60, 13*60 + 30 - 9*60)]  # Friday 13:00-13:30
    }

    # Define busy times for Eric (in minutes from 9:00)
    eric_busy = {
        0: [(9*60 - 9*60, 17*60 - 9*60)],       # Monday 9:00-17:00
        1: [(9*60 - 9*60, 17*60 - 9*60)],       # Tuesday 9:00-17:00
        2: [(9*60 - 9*60, 11*60 + 30 - 9*60),   # Wednesday 9:00-11:30
            (12*60 - 9*60, 14*60 - 9*60),       # Wednesday 12:00-14:00
            (14*60 + 30 - 9*60, 16*60 + 30 - 9*60)], # Wednesday 14:30-16:30
        3: [(9*60 - 9*60, 17*60 - 9*60)],       # Thursday 9:00-17:00
        4: [(9*60 - 9*60, 11*60 - 9*60),        # Friday 9:00-11:00
            (11*60 + 30 - 9*60, 17*60 - 9*60)]  # Friday 11:30-17:00
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
    s.add(is_available(eugene_busy, day, start_time))
    s.add(is_available(eric_busy, day, start_time))

    # Eric prefers to avoid Wednesday (day=2), so we'll try other days first
    # We'll use optimization to minimize (day_penalty + start_time)
    day_penalty = If(day == 2, 1000, 0)  # Penalize Wednesday
    objective = day_penalty + start_time
    opt = Optimize()
    opt.add(s.assertions())
    opt.minimize(objective)

    # Check if a solution exists
    if opt.check() == sat:
        model = opt.model()
        day_val = model[day].as_long()
        start = model[start_time].as_long()
        
        # Convert to human-readable format
        days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
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