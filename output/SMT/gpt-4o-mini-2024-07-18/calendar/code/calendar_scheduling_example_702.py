from z3 import *

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define busy times for each participant (in minutes from midnight)
busy_times = {
    "Robert": {
        "Monday": [
            (11 * 60, 11 * 60 + 30),  # 11:00 - 11:30
            (14 * 60, 14 * 60 + 30),   # 14:00 - 14:30
            (15 * 60 + 30, 16 * 60)     # 15:30 - 16:00
        ],
        "Tuesday": [
            (10 * 60 + 30, 11 * 60),   # 10:30 - 11:00
            (15 * 60, 15 * 60 + 30)     # 15:00 - 15:30
        ],
        "Wednesday": [
            (10 * 60, 11 * 60),         # 10:00 - 11:00
            (11 * 60 + 30, 12 * 60),    # 11:30 - 12:00
            (12 * 60 + 30, 13 * 60),    # 12:30 - 1:00
            (13 * 60 + 30, 14 * 60),    # 1:30 - 2:00
            (15 * 60, 15 * 60 + 30),     # 15:00 - 15:30
            (16 * 60, 16 * 60 + 30)      # 16:00 - 16:30
        ]
    },
    "Ralph": {
        "Monday": [
            (10 * 60, 13 * 60 + 30),    # 10:00 - 1:30
            (14 * 60, 14 * 60 + 30),    # 14:00 - 14:30
            (15 * 60, 17 * 60)           # 15:00 - 5:00
        ],
        "Tuesday": [
            (9 * 60, 9 * 60 + 30),       # 9:00 - 9:30
            (10 * 60, 10 * 60 + 30),     # 10:00 - 10:30
            (11 * 60, 11 * 60 + 30),     # 11:00 - 11:30
            (12 * 60, 13 * 60),          # 12:00 - 1:00
            (14 * 60, 15 * 60 + 30),     # 14:00 - 3:30
            (16 * 60, 17 * 60)           # 4:00 - 5:00
        ],
        "Wednesday": [
            (10 * 60 + 30, 11 * 60),     # 10:30 - 11:00
            (11 * 60, 12 * 60),          # 11:30 - 12:00
            (13 * 60, 14 * 60 + 30),     # 1:00 - 2:30
            (16 * 60 + 30, 17 * 60)      # 4:30 - 5:00
        ]
    }
}

# Initialize the Z3 solver
solver = Solver()

# Variable for the start time of the meeting and the day
start_time = Int('start_time')
day = String('day')  # Day of the week (Monday, Tuesday, Wednesday)

# Constraints: the meeting must occur during work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Function to add busy time constraints based on the participant and day
def add_busy_constraints(participant, busy_times):
    if day in busy_times:
        for busy_start, busy_end in busy_times[day]:
            # Add constraints to avoid busy times
            solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Check available times on Monday, Tuesday, and Wednesday
meeting_days = ["Monday", "Tuesday", "Wednesday"]
meeting_time_found = False

for meeting_day in meeting_days:
    # Clear existing constraints for the day variable
    solver.push()
    
    # Assign the current day for the meeting
    solver.add(day == meeting_day)

    # Add busy constraints for both participants
    add_busy_constraints("Robert", busy_times["Robert"])
    add_busy_constraints("Ralph", busy_times["Ralph"])

    # Add Robert's preference: avoid more meetings on Monday
    if meeting_day == "Monday":
        continue  # Skip Monday

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