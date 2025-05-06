from z3 import *

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define busy times for each participant (in minutes from midnight)
busy_times = {
    "Jesse": {
        "Monday": [
            (13 * 60 + 30, 14 * 60),  # 13:30 to 14:00
            (14 * 60 + 30, 15 * 60)   # 14:30 to 15:00
        ],
        "Tuesday": [
            (9 * 60, 9 * 60 + 30),    # 9:00 to 9:30
            (13 * 60, 13 * 60 + 30),   # 13:00 to 13:30
            (14 * 60, 15 * 60)         # 14:00 to 15:00
        ]
    },
    "Lawrence": {
        "Monday": [
            (9 * 60, 17 * 60)          # 9:00 to 17:00 (busy all day)
        ],
        "Tuesday": [
            (9 * 60 + 30, 10 * 60 + 30), # 9:30 to 10:30
            (11 * 60 + 30, 12 * 60 + 30), # 11:30 to 12:30
            (13 * 60, 13 * 60 + 30),   # 13:00 to 13:30
            (14 * 60, 15 * 60),        # 14:00 to 15:00
            (15 * 60 + 30, 16 * 60 + 30)  # 15:30 to 16:30
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

# Function to add busy time constraints based on a participant's availability
def add_busy_constraints(participant, day_name):
    if day_name in busy_times[participant]:
        for busy_start, busy_end in busy_times[participant][day_name]:
            # Ensure the meeting does not overlap with busy times
            solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Check available times on Monday and Tuesday
meeting_days = ["Monday", "Tuesday"]
meeting_time_found = False

for meeting_day in meeting_days:
    # Clear existing constraints for the day variable
    solver.push()
    
    # Assign the current day for the meeting
    solver.add(day == meeting_day)

    # Add busy constraints for both participants
    add_busy_constraints("Jesse", meeting_day)
    add_busy_constraints("Lawrence", meeting_day)

    # Add Lawrence's preference: cannot meet on Tuesday after 16:30
    if meeting_day == "Tuesday":
        solver.add(start_time <= (16 * 60 + 30))  # 16:30 in minutes

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