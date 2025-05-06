from z3 import *

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define busy times for each participant (in minutes from midnight)
busy_times = {
    "Amy": {
        "Wednesday": [
            (11 * 60, 11 * 60 + 30),  # 11:00 - 11:30
            (13 * 60 + 30, 14 * 60)    # 1:30 - 2:00
        ]
    },
    "Pamela": {
        "Monday": [
            (9 * 60, 10 * 60 + 30),   # 9:00 - 10:30
            (11 * 60, 16 * 60 + 30)   # 11:00 - 4:30
        ],
        "Tuesday": [
            (9 * 60, 9 * 60 + 30),     # 9:00 - 9:30
            (10 * 60, 17 * 60)         # 10:00 - 5:00
        ],
        "Wednesday": [
            (9 * 60, 9 * 60 + 30),     # 9:00 - 9:30
            (10 * 60, 11 * 60),        # 10:00 - 11:00
            (11 * 60 + 30, 13 * 60 + 30), # 11:30 - 1:30
            (14 * 60 + 30, 15 * 60),   # 2:30 - 3:00
            (16 * 60, 16 * 60 + 30)    # 4:00 - 4:30
        ]
    }
}

# Initialize the Z3 solver
solver = Solver()

# Variable for the start time of the meeting
start_time = Int('start_time')
day = String('day')  # Variable for the day of the meeting

# Constraints: the meeting must occur during work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Function to add busy time constraints for both participants
def add_busy_constraints(participant, participant_busy_times):
    for busy_start, busy_end in participant_busy_times:
        solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Check available times on Monday, Tuesday, and Wednesday
days = ["Monday", "Tuesday", "Wednesday"]
meeting_time_found = False

for meeting_day in days:
    # Clear existing constraints for the day variable
    solver.push()
    # Assign the current day for the meeting
    solver.add(day == meeting_day)
    
    # Add busy constraints based on the current day
    if meeting_day in busy_times["Amy"]:
        add_busy_constraints("Amy", busy_times["Amy"][meeting_day])
    
    if meeting_day in busy_times["Pamela"]:
        add_busy_constraints("Pamela", busy_times["Pamela"][meeting_day])
    
    # Add Pamela's preference constraints
    if meeting_day == "Monday":
        # Avoid more meetings on Monday
        solver.add(start_time >= work_start)  # Not more meetings
    elif meeting_day == "Tuesday":
        # Avoid meetings before 16:00 on Tuesday
        solver.add(start_time >= (16 * 60))
    elif meeting_day == "Wednesday":
        # Avoid meetings before 16:00 on Wednesday
        solver.add(start_time >= (16 * 60))

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