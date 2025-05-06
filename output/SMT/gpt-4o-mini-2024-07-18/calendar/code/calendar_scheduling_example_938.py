from z3 import *

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define busy times for each participant (in minutes from midnight)
busy_times = {
    "Eugene": {
        "Monday": [
            (11 * 60, 12 * 60),        # 11:00 to 12:00
            (13 * 60 + 30, 14 * 60),   # 1:30 to 2:00
            (14 * 60 + 30, 15 * 60),   # 2:30 to 3:00
            (16 * 60, 16 * 60 + 30)    # 4:00 to 4:30
        ],
        "Tuesday": [],
        "Wednesday": [
            (9 * 60, 9 * 60 + 30),     # 9:00 to 9:30
            (11 * 60, 11 * 60 + 30),   # 11:00 to 11:30
            (12 * 60, 12 * 60 + 30),   # 12:00 to 12:30
            (13 * 60 + 30, 15 * 60)    # 1:30 to 3:00
        ],
        "Thursday": [
            (9 * 60 + 30, 10 * 60),    # 9:30 to 10:00
            (11 * 60, 12 * 60 + 30)    # 11:00 to 12:30
        ],
        "Friday": [
            (10 * 60 + 30, 11 * 60),    # 10:30 to 11:00
            (12 * 60, 12 * 60 + 30),     # 12:00 to 12:30
            (13 * 60, 13 * 60 + 30)      # 1:00 to 1:30
        ]
    },
    "Eric": {
        "Monday": [
            (9 * 60, 17 * 60)           # Busy all day
        ],
        "Tuesday": [
            (9 * 60, 17 * 60)           # Busy all day
        ],
        "Wednesday": [
            (9 * 60, 11 * 60 + 30),     # 9:00 to 11:30
            (12 * 60, 14 * 60),         # 12:00 to 2:00
            (14 * 60 + 30, 16 * 60 + 30) # 2:30 to 5:00
        ],
        "Thursday": [
            (9 * 60, 17 * 60)           # Busy all day
        ],
        "Friday": [
            (9 * 60, 11 * 60),           # 9:00 to 11:00
            (11 * 60 + 30, 17 * 60)      # 11:30 to 5:00
        ]
    }
}

# Initialize Z3 solver
solver = Solver()

# Variable for the start time of the meeting and the day
start_time = Int('start_time')
day = String('day')  # Day of the week

# Constraints: the meeting must occur during work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Function to add busy time constraints
def add_busy_constraints(participant, day_name):
    for busy_start, busy_end in busy_times[participant][day_name]:
        # Ensure the meeting does not overlap with busy times
        solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Check available times for Monday, Tuesday, Wednesday, Thursday, and Friday
meeting_days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
meeting_time_found = False

for meeting_day in meeting_days:
    solver.push()  # Push the current state to backtrack later
    
    # Assign the current day for the meeting
    solver.add(day == meeting_day)

    # Add busy constraints for both participants
    add_busy_constraints("Eugene", meeting_day)
    add_busy_constraints("Eric", meeting_day)

    # Add Eric's preference: avoid more meetings on Wednesday
    if meeting_day == "Wednesday":
        continue  # Skip Wednesday for Eric

    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start_time].as_long()
        meeting_end = meeting_start + meeting_duration
        print(f"Meeting can be scheduled on {meeting_day} from {meeting_start // 60:02}:{meeting_start % 60:02} to {meeting_end // 60:02}:{meeting_end % 60:02}")
        meeting_time_found = True
        break  # Exit if meeting time is found
    
    solver.pop()  # Pop the last constraints to try the next day

if not meeting_time_found:
    print("No available time found for the meeting.")