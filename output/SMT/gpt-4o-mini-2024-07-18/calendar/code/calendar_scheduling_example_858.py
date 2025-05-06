from z3 import *

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 60  # Meeting duration in minutes

# Define busy times for each participant (in minutes from midnight)
busy_times = {
    "Carl": {
        "Monday": [
            (11 * 60, 11 * 60 + 30)   # 11:00 to 11:30
        ],
        "Tuesday": [
            (14 * 60 + 30, 15 * 60)    # 2:30 to 3:00
        ],
        "Wednesday": [
            (10 * 60, 11 * 60 + 30),   # 10:00 to 11:30
            (13 * 60, 13 * 60 + 30)    # 1:00 to 1:30
        ],
        "Thursday": [
            (13 * 60 + 30, 14 * 60),    # 1:30 to 2:00
            (16 * 60, 16 * 60 + 30)      # 4:00 to 4:30
        ]
    },
    "Margaret": {
        "Monday": [
            (9 * 60, 10 * 60 + 30),     # 9:00 to 10:30
            (11 * 60, 17 * 60)           # 11:00 to 5:00
        ],
        "Tuesday": [
            (9 * 60 + 30, 12 * 60),      # 9:30 to 12:00
            (13 * 60 + 30, 14 * 60),     # 1:30 to 2:00
            (15 * 60 + 30, 17 * 60)      # 3:30 to 5:00 
        ],
        "Wednesday": [
            (9 * 60 + 30, 12 * 60),      # 9:30 to 12:00
            (12 * 60 + 30, 13 * 60),     # 12:30 to 1:00
            (13 * 60 + 30, 14 * 60 + 30), # 1:30 to 2:30
            (15 * 60, 17 * 60)           # 3:00 to 5:00
        ],
        "Thursday": [
            (10 * 60, 12 * 60),          # 10:00 to 12:00
            (12 * 60 + 30, 14 * 60),      # 12:30 to 2:00
            (14 * 60 + 30, 17 * 60)      # 2:30 to 5:00 
        ]
    }
}

# Initialize Z3 Solver
solver = Solver()

# Variable for the start time of the meeting
start_time = Int('start_time')
day = String('day')  # Day of the meeting

# Constraints: the meeting must occur during work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Function to add busy time constraints for each participant on a given day
def add_busy_constraints(participant, day_name):
    if day_name in busy_times[participant]:
        for busy_start, busy_end in busy_times[participant][day_name]:
            solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Check available times on working days: Monday, Tuesday, Wednesday, Thursday
meeting_days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
meeting_time_found = False

for meeting_day in meeting_days:
    # Push the current state to backtrack later
    solver.push()

    # Assign the current day for the meeting
    solver.add(day == meeting_day)

    # Add busy constraints for both participants
    add_busy_constraints("Carl", meeting_day)
    add_busy_constraints("Margaret", meeting_day)

    # Add Carl's preference: avoid meetings on Thursday
    if meeting_day == "Thursday":
        solver.pop()  # Skip this day
        continue

    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start_time].as_long()
        meeting_end = meeting_start + meeting_duration
        print(f"Meeting can be scheduled on {meeting_day} from {meeting_start // 60:02}:{meeting_start % 60:02} to {meeting_end // 60:02}:{meeting_end % 60:02}")
        meeting_time_found = True
        break  # Exit upon finding the earliest meeting time

    # Pop the latest constraints
    solver.pop()

# If no time was found, print this message
if not meeting_time_found:
    print("No available time found for the meeting.")