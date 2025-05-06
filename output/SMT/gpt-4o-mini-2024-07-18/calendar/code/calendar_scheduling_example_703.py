from z3 import *

# Define the work hours and meeting durations
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 60  # Meeting duration in minutes

# Define busy times for each participant (in minutes from midnight)
busy_times = {
    "Stephanie": {
        "Monday": [
            (9 * 60 + 30, 10 * 60),    # 9:30 to 10:00
            (10 * 60 + 30, 11 * 60),   # 10:30 to 11:00
            (11 * 60 + 30, 12 * 60),   # 11:30 to 12:00
            (14 * 60, 14 * 60 + 30)    # 2:00 to 2:30
        ],
        "Tuesday": [
            (12 * 60, 13 * 60)          # 12:00 to 1:00
        ],
        "Wednesday": [
            (9 * 60, 10 * 60),          # 9:00 to 10:00
            (13 * 60, 14 * 60)          # 1:00 to 2:00
        ]
    },
    "Betty": {
        "Monday": [
            (9 * 60, 10 * 60),           # 9:00 to 10:00
            (11 * 60, 11 * 60 + 30),     # 11:00 to 11:30
            (14 * 60 + 30, 15 * 60),     # 2:30 to 3:00
            (15 * 60 + 30, 16 * 60)      # 3:30 to 4:00
        ],
        "Tuesday": [
            (9 * 60, 9 * 60 + 30),       # 9:00 to 9:30
            (11 * 60 + 30, 12 * 60),     # 11:30 to 12:00
            (12 * 60 + 30, 14 * 60 + 30), # 12:30 to 2:30
            (15 * 60 + 30, 16 * 60)      # 3:30 to 4:00
        ],
        "Wednesday": [
            (10 * 60, 11 * 60 + 30),     # 10:00 to 11:30
            (12 * 60, 14 * 60),           # 12:00 to 2:00
            (14 * 60 + 30, 17 * 60)      # 2:30 to 5:00
        ]
    }
}

# Initialize Z3 Solver
solver = Solver()

# Variable for the proposed start time of the meeting
start_time = Int('start_time')
day = String('day')  # Day of the meeting

# Constraints: the meeting must occur during work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Function to add busy time constraints for each participant on a given day
def add_busy_constraints(participant, day_name):
    if day_name in busy_times[participant]:
        for busy_start, busy_end in busy_times[participant][day_name]:
            # Ensure that the proposed meeting does not overlap with busy times
            solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Check available times on working days: Monday, Tuesday, Wednesday
meeting_days = ["Monday", "Tuesday", "Wednesday"]
meeting_time_found = False

for meeting_day in meeting_days:
    # Push the current state to backtrack later
    solver.push()

    # Assign the current day for the meeting
    solver.add(day == meeting_day)

    # Add busy constraints for both participants
    add_busy_constraints("Stephanie", meeting_day)
    add_busy_constraints("Betty", meeting_day)

    # Add Stephanie's preference: She would like to avoid more meetings on Monday
    if meeting_day == "Monday":
        solver.add(start_time >= (14 * 60))  # After 2:00 PM

    # Add Betty's restriction: cannot meet on Tuesday after 12:30
    if meeting_day == "Tuesday":
        solver.add(start_time <= (12 * 60 + 30))  # 12:30 PM

    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start_time].as_long()
        meeting_end = meeting_start + meeting_duration
        print(f"Meeting can be scheduled on {meeting_day} from "
              f"{meeting_start // 60:02}:{meeting_start % 60:02} to "
              f"{meeting_end // 60:02}:{meeting_end % 60:02}")
        meeting_time_found = True
        break  # Exit upon finding the earliest meeting time

    # Pop the last constraints to check the next day
    solver.pop()

# If no time was found, print this message
if not meeting_time_found:
    print("No available time found for the meeting.")