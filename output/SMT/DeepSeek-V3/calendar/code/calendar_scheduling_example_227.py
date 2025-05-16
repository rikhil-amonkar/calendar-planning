from z3 import *

def find_meeting_time():
    # Create solver instance
    s = Solver()

    # Define start time in minutes from 9:00 (0 = 9:00, 480 = 17:00)
    start_time = Int('start_time')
    meeting_duration = 30  # 30 minutes
    s.add(start_time >= 0, start_time <= 480 - meeting_duration)

    # Define busy times for each participant (in minutes from 9:00)
    busy_times = {
        'Natalie': [],  # Free all day
        'David': [
            (11*60 + 30 - 9*60, 12*60 - 9*60),    # 11:30-12:00
            (14*60 + 30 - 9*60, 15*60 - 9*60)      # 14:30-15:00
        ],
        'Douglas': [
            (9*60 + 30 - 9*60, 10*60 - 9*60),     # 9:30-10:00
            (11*60 + 30 - 9*60, 12*60 - 9*60),     # 11:30-12:00
            (13*60 - 9*60, 13*60 + 30 - 9*60),     # 13:00-13:30
            (14*60 + 30 - 9*60, 15*60 - 9*60)      # 14:30-15:00
        ],
        'Ralph': [
            (9*60 - 9*60, 9*60 + 30 - 9*60),      # 9:00-9:30
            (10*60 - 9*60, 11*60 - 9*60),          # 10:00-11:00
            (11*60 + 30 - 9*60, 12*60 + 30 - 9*60), # 11:30-12:30
            (13*60 + 30 - 9*60, 15*60 - 9*60),     # 13:30-15:00
            (15*60 + 30 - 9*60, 16*60 - 9*60),     # 15:30-16:00
            (16*60 + 30 - 9*60, 17*60 - 9*60)      # 16:30-17:00
        ],
        'Jordan': [
            (9*60 - 9*60, 10*60 - 9*60),          # 9:00-10:00
            (12*60 - 9*60, 12*60 + 30 - 9*60),     # 12:00-12:30
            (13*60 - 9*60, 13*60 + 30 - 9*60),     # 13:00-13:30
            (14*60 + 30 - 9*60, 15*60 - 9*60),     # 14:30-15:00
            (15*60 + 30 - 9*60, 17*60 - 9*60)      # 15:30-17:00
        ]
    }

    # Function to check if time is available for a person
    def is_available(person, time):
        constraints = []
        for (busy_start, busy_end) in busy_times[person]:
            constraints.append(Or(time >= busy_end, time + meeting_duration <= busy_start))
        return And(constraints) if constraints else True

    # Add constraints for all participants
    participants = ['Natalie', 'David', 'Douglas', 'Ralph', 'Jordan']
    for person in participants:
        s.add(is_available(person, start_time))

    # David's constraint to not meet before 14:00
    s.add(start_time >= (14*60 - 9*60))

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