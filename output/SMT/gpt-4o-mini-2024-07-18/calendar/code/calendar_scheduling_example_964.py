from z3 import *

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 60  # Meeting duration in minutes

# Define busy times for each participant (in minutes from midnight)
busy_times = {
    "Betty": {
        "Monday": [
            (10 * 60, 10 * 60 + 30),  # 10:00 - 10:30
            (11 * 60 + 30, 12 * 60 + 30),  # 11:30 - 12:30
            (16 * 60, 16 * 60 + 30)  # 16:00 - 16:30
        ],
        "Tuesday": [
            (9 * 60 + 30, 10 * 60),   # 9:30 - 10:00
            (10 * 60 + 30, 11 * 60),  # 10:30 - 11:00
            (12 * 60, 12 * 60 + 30),  # 12:00 - 12:30
            (13 * 60 + 30, 15 * 60),  # 13:30 - 15:00
            (16 * 60 + 30, 17 * 60)   # 16:30 - 17:00
        ],
        "Friday": [
            (9 * 60, 10 * 60),        # 9:00 - 10:00
            (11 * 60 + 30, 12 * 60),  # 11:30 - 12:00
            (12 * 60 + 30, 13 * 60),  # 12:30 - 13:00
            (14 * 60 + 30, 15 * 60)   # 14:30 - 15:00
        ]
    },
    "Megan": {
        "Monday": [
            (9 * 60, 17 * 60)          # 9:00 - 5:00 (busy all day)
        ],
        "Tuesday": [
            (9 * 60, 9 * 60 + 30),     # 9:00 - 9:30
            (10 * 60, 10 * 60 + 30),   # 10:00 - 10:30
            (12 * 60, 14 * 60),        # 12:00 - 2:00
            (15 * 60, 15 * 60 + 30),   # 3:00 - 3:30
            (16 * 60, 16 * 60 + 30)    # 4:00 - 4:30
        ],
        "Wednesday": [
            (9 * 60 + 30, 10 * 60 + 30),  # 9:30 - 10:30
            (11 * 60, 11 * 60 + 30),      # 11:00 - 11:30
            (12 * 60 + 30, 13 * 60),      # 12:30 - 1:00
            (13 * 60 + 30, 14 * 60 + 30), # 1:30 - 2:30
            (15 * 60 + 30, 17 * 60)       # 3:30 - 5:00
        ],
        "Thursday": [
            (9 * 60, 10 * 60 + 30),      # 9:00 - 10:30
            (11 * 60 + 30, 14 * 60),      # 11:30 - 2:00
            (14 * 60 + 30, 15 * 60),      # 2:30 - 3:00
            (15 * 60 + 30, 16 * 60 + 30)  # 3:30 - 4:30
        ],
        "Friday": [
            (9 * 60, 17 * 60)             # 9:00 - 5:00 (busy all day)
        ]
    }
}

# Initialize the Z3 solver
solver = Solver()

# Variable for the start time of the meeting and the day
start_time = Int('start_time')
day = String('day')  # Day of the week (Monday, Tuesday, Wednesday, Thursday, Friday)

# Constraints: the meeting must occur during work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Function to add busy time constraints based on the participant and day
def add_busy_constraints(participant, participant_busy_times):
    if participant in participant_busy_times:
        for busy_start, busy_end in participant_busy_times[participant]:
            # Add constraints to avoid busy times
            solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Check available times on Monday, Tuesday, Wednesday, Thursday, and Friday
meeting_days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
meeting_time_found = False

for meeting_day in meeting_days:
    # Clear existing constraints for the day variable
    solver.push()
    
    # Assign the current day for the meeting
    solver.add(day == meeting_day)

    # Add busy constraints for both participants
    add_busy_constraints("Betty", busy_times["Betty"])
    add_busy_constraints("Megan", busy_times["Megan"])
    
    # Add Betty's constraint: cannot meet on Wednesday or Thursday
    if meeting_day in ["Wednesday", "Thursday"]:
        continue  # Skip these days

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