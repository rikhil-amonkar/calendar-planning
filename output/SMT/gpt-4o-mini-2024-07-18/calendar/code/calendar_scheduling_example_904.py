from z3 import *

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define busy times for each participant (in minutes from midnight)
busy_times = {
    "Daniel": {
        "Monday": [
            (9 * 60 + 30, 10 * 60 + 30),  # 9:30 to 10:30
            (12 * 60, 12 * 60 + 30),       # 12:00 to 12:30
            (13 * 60, 14 * 60),             # 1:00 to 2:00
            (14 * 60 + 30, 15 * 60),       # 2:30 to 3:00
            (15 * 60 + 30, 16 * 60)        # 3:30 to 4:00
        ],
        "Tuesday": [
            (11 * 60, 12 * 60),            # 11:00 to 12:00
            (13 * 60, 13 * 60 + 30),       # 1:00 to 1:30
            (15 * 60 + 30, 16 * 60),       # 3:30 to 4:00
            (16 * 60 + 30, 17 * 60)        # 4:30 to 5:00
        ],
        "Wednesday": [
            (9 * 60, 10 * 60),              # 9:00 to 10:00
            (14 * 60, 14 * 60 + 30)         # 2:00 to 2:30
        ],
        "Thursday": [
            (10 * 60 + 30, 11 * 60),        # 10:30 to 11:00
            (12 * 60, 13 * 60),            # 12:00 to 1:00
            (14 * 60 + 30, 15 * 60),       # 2:30 to 3:00
            (15 * 60 + 30, 16 * 60)        # 3:30 to 4:00
        ],
        "Friday": [
            (9 * 60, 9 * 60 + 30),          # 9:00 to 9:30
            (11 * 60 + 30, 12 * 60),        # 11:30 to 12:00
            (13 * 60, 13 * 60 + 30),       # 1:00 to 1:30
            (16 * 60 + 30, 17 * 60)         # 4:30 to 5:00
        ]
    },
    "Bradley": {
        "Monday": [
            (9 * 60 + 30, 11 * 60),         # 9:30 to 11:00
            (11 * 60 + 30, 12 * 60),        # 11:30 to 12:00
            (12 * 60, 13 * 60),             # 12:00 to 1:00
            (14 * 60, 15 * 60)              # 2:00 to 3:00
        ],
        "Tuesday": [
            (10 * 60 + 30, 11 * 60),        # 10:30 to 11:00
            (12 * 60, 13 * 60),             # 12:00 to 1:00
            (13 * 60 + 30, 14 * 60),        # 1:30 to 2:00
            (15 * 60 + 30, 16 * 60 + 30)    # 3:30 to 4:30
        ],
        "Wednesday": [
            (9 * 60, 10 * 60),              # 9:00 to 10:00
            (11 * 60, 13 * 60),             # 11:00 to 1:00
            (13 * 60 + 30, 14 * 60),        # 1:30 to 2:00
            (14 * 60 + 30, 17 * 60)         # 2:30 to 5:00
        ],
        "Thursday": [
            (9 * 60, 12 * 60 + 30),         # 9:00 to 12:30
            (13 * 60 + 30, 14 * 60),        # 1:30 to 2:00
            (14 * 60 + 30, 15 * 60),        # 2:30 to 3:00
            (15 * 60 + 30, 16 * 60 + 30)    # 3:30 to 4:30
        ],
        "Friday": [
            (9 * 60, 9 * 60 + 30),          # 9:00 to 9:30
            (10 * 60, 12 * 60 + 30),        # 10:00 to 12:30
            (13 * 60, 13 * 60 + 30),        # 1:00 to 1:30
            (14 * 60, 14 * 60 + 30),        # 2:00 to 2:30
            (15 * 60 + 30, 16 * 60 + 30)    # 3:30 to 4:30
        ]
    }
}

# Initialize Z3 Solver
solver = Solver()

# Variable for the start time of the meeting
start_time = Int('start_time')
day = String('day')  # Day of the week

# Constraints: the meeting must occur during work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Function to add busy time constraints for each participant on a given day
def add_busy_constraints(participant, day_name):
    if day_name in busy_times[participant]:
        for busy_start, busy_end in busy_times[participant][day_name]:
            # Ensure the meeting does not overlap with busy times
            solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Check available times on working days: Monday, Tuesday, Wednesday, Thursday, Friday
meeting_days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
meeting_time_found = False

for meeting_day in meeting_days:
    solver.push()  # Push the current state to backtrack later
    
    # Assign the current day for the meeting
    solver.add(day == meeting_day)

    # Add busy constraints for both participants
    add_busy_constraints("Daniel", meeting_day)
    add_busy_constraints("Bradley", meeting_day)

    # Add Daniel's preference: no meetings on Wednesday or Thursday
    if meeting_day == "Wednesday" or meeting_day == "Thursday":
        solver.pop()  # If it's Wednesday or Thursday, skip this day
        continue

    # Add Bradley's preference: no meetings on Monday, Tuesday before 12:00, or Friday
    if meeting_day == "Monday":
        solver.add(start_time >= (12 * 60))  # Ensure meeting starts after 12:00
    elif meeting_day == "Tuesday":
        solver.add(start_time >= (12 * 60))  # Ensure meeting starts after 12:00
    elif meeting_day == "Friday":
        solver.pop()  # Skip Fridays as per Bradley's preference
        continue

    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start_time].as_long()
        meeting_end = meeting_start + meeting_duration
        print(f"Meeting can be scheduled on {meeting_day} from {meeting_start // 60:02}:{meeting_start % 60:02} to {meeting_end // 60:02}:{meeting_end % 60:02}")
        meeting_time_found = True
        break  # Exit upon finding the meeting time

    solver.pop()  # Pop the last constraints to check the next day

# If no time was found, print this message
if not meeting_time_found:
    print("No available time found for the meeting.")