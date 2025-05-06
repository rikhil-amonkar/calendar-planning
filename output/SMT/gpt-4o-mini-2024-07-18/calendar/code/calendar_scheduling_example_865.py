from z3 import *

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 60  # Meeting duration in minutes

# Define busy times for each participant (in minutes from midnight)
busy_times = {
    "Megan": {
        "Monday": [
            (13 * 60, 13 * 60 + 30),   # 13:00 to 13:30
            (14 * 60, 15 * 60 + 30)     # 14:00 to 15:30
        ],
        "Tuesday": [
            (9 * 60, 9 * 60 + 30),      # 9:00 to 9:30
            (12 * 60, 12 * 60 + 30),    # 12:00 to 12:30
            (16 * 60, 17 * 60)          # 16:00 to 17:00
        ],
        "Wednesday": [
            (9 * 60 + 30, 10 * 60),     # 9:30 to 10:00
            (10 * 60 + 30, 11 * 60 + 30), # 10:30 to 11:30
            (12 * 60 + 30, 14 * 60),     # 12:30 to 14:00
            (16 * 60, 16 * 60 + 30)      # 16:00 to 16:30
        ],
        "Thursday": [
            (13 * 60 + 30, 14 * 60 + 30), # 13:30 to 14:30
            (15 * 60, 15 * 60 + 30)       # 15:00 to 15:30
        ]
    },
    "Daniel": {
        "Monday": [
            (10 * 60, 11 * 60 + 30),     # 10:00 to 11:30
            (12 * 60 + 30, 15 * 60)      # 12:30 to 15:00
        ],
        "Tuesday": [
            (9 * 60, 10 * 60),           # 9:00 to 10:00
            (10 * 60 + 30, 17 * 60)      # 10:30 to 17:00
        ],
        "Wednesday": [
            (9 * 60, 10 * 60),           # 9:00 to 10:00
            (10 * 60 + 30, 11 * 60 + 30), # 10:30 to 11:30
            (12 * 60, 17 * 60)           # 12:00 to 17:00
        ],
        "Thursday": [
            (9 * 60, 12 * 60),           # 9:00 to 12:00
            (12 * 60 + 30, 14 * 60 + 30), # 12:30 to 14:30
            (15 * 60, 15 * 60 + 30),      # 15:00 to 15:30
            (16 * 60, 17 * 60)            # 16:00 to 17:00
        ]
    }
}

# Initialize Z3 Solver
solver = Solver()

# Variable for the start time of the meeting
start_time = Int('start_time')
day = String('day')  # Day of the meeting

# Constraints to ensure the meeting falls within work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Function to add busy time constraints for each participant
def add_busy_constraints(participant, day_name):
    if day_name in busy_times[participant]:
        for busy_start, busy_end in busy_times[participant][day_name]:
            # Ensure that the proposed meeting does not overlap with busy times
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
    add_busy_constraints("Megan", meeting_day)
    add_busy_constraints("Daniel", meeting_day)

    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start_time].as_long()
        meeting_end = meeting_start + meeting_duration
        print(f"Meeting can be scheduled on {meeting_day} from {meeting_start // 60:02}:{meeting_start % 60:02} to {meeting_end // 60:02}:{meeting_end % 60:02}")
        meeting_time_found = True
        break  # Exit upon finding the earliest meeting time

    solver.pop()  # Pop the last constraints to check the next day

# If no time was found, print this message
if not meeting_time_found:
    print("No available time found for the meeting.")