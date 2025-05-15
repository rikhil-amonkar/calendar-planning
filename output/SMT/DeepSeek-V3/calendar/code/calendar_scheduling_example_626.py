from z3 import *

def find_meeting_time():
    # Create a solver instance
    s = Solver()

    # Define the possible days (Monday and Tuesday)
    days = ['Monday', 'Tuesday']
    day = Int('day')
    s.add(day >= 0, day < len(days))  # 0 for Monday, 1 for Tuesday

    # Define the possible start times (in minutes from 9:00)
    start_time = Int('start_time')
    # Meeting duration is 1 hour (60 minutes)
    meeting_duration = 60
    # Work hours are from 9:00 to 17:00 (480 minutes in total, from 0 to 480 - 60)
    s.add(start_time >= 0, start_time <= 480 - meeting_duration)

    # Convert start_time to hours and minutes for readability
    start_hour = start_time // 60 + 9
    start_minute = start_time % 60

    # Patricia's busy times (in minutes from 9:00)
    patricia_busy = {
        'Monday': [(10*60 - 9*60, 10*60 + 30 - 9*60),  # 10:00-10:30
                   (11*60 + 30 - 9*60, 12*60 - 9*60),  # 11:30-12:00
                   (13*60 - 9*60, 13*60 + 30 - 9*60),  # 13:00-13:30
                   (14*60 + 30 - 9*60, 15*60 + 30 - 9*60),  # 14:30-15:30
                   (16*60 - 9*60, 16*60 + 30 - 9*60)], # 16:00-16:30
        'Tuesday': [(10*60 - 9*60, 10*60 + 30 - 9*60),  # 10:00-10:30
                    (11*60 - 9*60, 12*60 - 9*60),      # 11:00-12:00
                    (14*60 - 9*60, 16*60 - 9*60),      # 14:00-16:00
                    (16*60 + 30 - 9*60, 17*60 - 9*60)] # 16:30-17:00
    }

    # Jesse's busy times (in minutes from 9:00)
    jesse_busy = {
        'Monday': [(9*60 - 9*60, 17*60 - 9*60)],  # 9:00-17:00 (entire day)
        'Tuesday': [(11*60 - 9*60, 11*60 + 30 - 9*60),  # 11:00-11:30
                    (12*60 - 9*60, 12*60 + 30 - 9*60),  # 12:00-12:30
                    (13*60 - 9*60, 14*60 - 9*60),       # 13:00-14:00
                    (14*60 + 30 - 9*60, 15*60 - 9*60),   # 14:30-15:00
                    (15*60 + 30 - 9*60, 17*60 - 9*60)]  # 15:30-17:00
    }

    # Define constraints for Patricia and Jesse's busy times
    def is_busy(person_busy, day_idx, time):
        day_name = days[day_idx]
        busy_times = person_busy.get(day_name, [])
        constraints = []
        for (busy_start, busy_end) in busy_times:
            # The meeting should not overlap with any busy time
            constraints.append(Or(time >= busy_end, time + meeting_duration <= busy_start))
        return And(constraints) if constraints else True

    # Add constraints for Patricia
    s.add(is_busy(patricia_busy, day, start_time))
    # Add constraints for Jesse
    s.add(is_busy(jesse_busy, day, start_time))

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        day_idx = model[day].as_long()
        start = model[start_time].as_long()
        start_hour = start // 60 + 9
        start_minute = start % 60
        end = start + meeting_duration
        end_hour = end // 60 + 9
        end_minute = end % 60
        return {
            'day': days[day_idx],
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