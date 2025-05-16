from z3 import *

def find_meeting_time():
    # Create solver instance
    s = Solver()

    # Define start time in minutes from 9:00 (0 = 9:00, 480 = 17:00)
    start_time = Int('start_time')
    meeting_duration = 30  # 30 minutes
    s.add(start_time >= 0, start_time <= 480 - meeting_duration)

    # Define busy times for each participant (in minutes from 9:00)
    adam_busy = [
        (9*60 + 30 - 9*60, 10*60 - 9*60),    # 9:30-10:00
        (12*60 + 30 - 9*60, 13*60 - 9*60),    # 12:30-13:00
        (14*60 + 30 - 9*60, 15*60 - 9*60),    # 14:30-15:00
        (16*60 + 30 - 9*60, 17*60 - 9*60)     # 16:30-17:00
    ]

    roy_busy = [
        (10*60 - 9*60, 11*60 - 9*60),        # 10:00-11:00
        (11*60 + 30 - 9*60, 13*60 - 9*60),    # 11:30-13:00
        (13*60 + 30 - 9*60, 14*60 + 30 - 9*60), # 13:30-14:30
        (16*60 + 30 - 9*60, 17*60 - 9*60)     # 16:30-17:00
    ]

    # Function to check if time is available for a person
    def is_available(busy_slots, time):
        constraints = []
        for (busy_start, busy_end) in busy_slots:
            constraints.append(Or(time >= busy_end, time + meeting_duration <= busy_start))
        return And(constraints)

    # Add constraints for both participants
    s.add(is_available(adam_busy, start_time))
    s.add(is_available(roy_busy, start_time))

    # To find the earliest time, we'll minimize start_time
    objective = start_time
    opt = Optimize()
    opt.add(s.assertions())
    opt.minimize(objective)

    # Check if a solution exists
    if opt.check() == sat:
        model = opt.model()
        start = model[start_time].as_long()
        
        # Convert to human-readable format
        start_hour = start // 60 + 9
        start_minute = start % 60
        end = start + meeting_duration
        end_hour = end // 60 + 9
        end_minute = end % 60
        
        return {
            'day': 'Monday',
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