from z3 import *

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define busy times for each participant (in minutes from midnight)
busy_times = {
    "Betty": {
        "Monday": [
            (10 * 60, 10 * 60 + 30),
            (13 * 60 + 30, 14 * 60),
            (15 * 60, 15 * 60 + 30),
            (16 * 60, 17 * 60)
        ],
        "Tuesday": [
            (9 * 60, 9 * 60 + 30),
            (11 * 60 + 30, 12 * 60),
            (12 * 60 + 30, 13 * 60),
            (13 * 60 + 30, 14 * 60),
            (16 * 60 + 30, 17 * 60)
        ],
        "Wednesday": [
            (9 * 60 + 30, 10 * 60 + 30),
            (13 * 60, 13 * 60 + 30),
            (14 * 60, 14 * 60 + 30)
        ],
        "Thursday": [
            (9 * 60 + 30, 10 * 60),
            (11 * 60 + 30, 12 * 60),
            (14 * 60, 14 * 60 + 30),
            (15 * 60, 15 * 60 + 30),
            (16 * 60 + 30, 17 * 60)
        ]
    },
    "Scott": {
        "Monday": [
            (9 * 60 + 30, 15 * 60),
            (15 * 60 + 30, 16 * 60),
            (16 * 60 + 30, 17 * 60)
        ],
        "Tuesday": [
            (9 * 60, 9 * 60 + 30),
            (10 * 60, 11 * 60),
            (11 * 60 + 30, 12 * 60),
            (12 * 60 + 30, 13 * 60),
            (14 * 60, 15 * 60),
            (16 * 60, 16 * 60 + 30)
        ],
        "Wednesday": [
            (9 * 60 + 30, 12 * 60 + 30),
            (13 * 60, 13 * 60 + 30),
            (14 * 60, 14 * 60 + 30),
            (15 * 60, 15 * 60 + 30),
            (16 * 60, 16 * 60 + 30)
        ],
        "Thursday": [
            (9 * 60, 9 * 60 + 30),
            (10 * 60, 10 * 60 + 30),
            (11 * 60, 12 * 60),
            (12 * 60 + 30, 13 * 60),
            (15 * 60, 16 * 60),
            (16 * 60 + 30, 17 * 60)
        ]
    }
}

# Initialize the Z3 solver
solver = Solver()

# Variable for the start time of the meeting and the day
start_time = Int('start_time')
day = String('day')  # Day of the week

# Constraints: the meeting must occur during work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Function to add busy time constraints based on availability
def add_busy_constraints(participant, day_name):
    for busy_start, busy_end in busy_times[participant][day_name]:
        solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Check available times on Monday, Tuesday, Wednesday, and Thursday
meeting_days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
meeting_time_found = False

for meeting_day in meeting_days:
    # Clear existing constraints for the day variable
    solver.push()
    
    # Assign the current day for the meeting
    solver.add(day == meeting_day)

    # Add busy constraints for both participants
    add_busy_constraints("Betty", meeting_day)
    add_busy_constraints("Scott", meeting_day)

    # Add Betty's constraints: cannot meet on Monday or Tuesday, and cannot meet before 15:00 on Thursday
    if meeting_day == "Monday" or meeting_day == "Tuesday":
        continue  # Skip these days for Betty
    if meeting_day == "Thursday":
        solver.add(start_time >= (15 * 60))  # Start time should be no earlier than 3 PM

    # Add Scott's preference: avoid meetings on Wednesday
    if meeting_day == "Wednesday":
        continue  # Skip Wednesday for Scott

    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start_time].as_long()
        meeting_end = meeting_start + meeting_duration
        print(f"Meeting can be scheduled on {meeting_day} from {meeting_start // 60:02}:{meeting_start % 60:02} to {meeting_end // 60:02}:{meeting_end % 60:02}")
        meeting_time_found = True
        break  # Exit the loop upon finding the earliest meeting time
    
    # Pop the last constraints to check the next day
    solver.pop()

if not meeting_time_found:
    print("No available time found for the meeting.")