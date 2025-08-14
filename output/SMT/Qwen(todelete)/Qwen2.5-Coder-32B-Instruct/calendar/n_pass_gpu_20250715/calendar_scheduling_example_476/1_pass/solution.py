from z3 import *

# Define the participants and their availability
participants = {
    "Daniel": [(9*60, 17*60)],  # Available from 9:00 to 17:00
    "Kathleen": [(9*60, 14*30), (15*30, 17*60)],  # Busy from 14:30 to 15:30
    "Carolyn": [(9*60, 12*00), (12*30, 13*00), (13*30, 17*60)],  # Busy from 12:00 to 12:30, 13:00 to 13:30
    "Roger": [(9*60, 17*60)],  # Available from 9:00 to 17:00, prefers after 12:30
    "Cheryl": [(9*30, 10*00), (11*30, 12*30), (13*30, 14*00)],  # Busy from 9:00 to 9:30, 10:00 to 11:30, 12:30 to 13:30, 14:00 to 17:00
    "Virginia": [(9*00, 9*30), (11*30, 12*00), (13*30, 14*30), (15*30, 16*00)],  # Busy from 9:30 to 11:30, 12:00 to 12:30, 13:00 to 13:30, 14:30 to 15:30, 16:00 to 17:00
    "Angela": [(9*00, 9*30), (10*00, 10*30), (11*30, 12*00), (13*30, 14*00), (16*30, 17*00)]  # Busy from 9:30 to 10:00, 10:30 to 11:30, 12:00 to 12:30, 13:00 to 13:30, 14:00 to 16:30
}

# Create a solver instance
solver = Solver()

# Define the meeting start time variable in minutes since 00:00
meeting_start = Int('meeting_start')
meeting_duration = 30  # Meeting duration is 30 minutes

# Add constraints for each participant
for participant, availabilities in participants.items():
    # Create a disjunction of all available time slots for the participant
    participant_constraints = Or([And(meeting_start >= start, meeting_start + meeting_duration <= end) for start, end in availabilities])
    solver.add(participant_constraints)

# Roger's preference to meet after 12:30
solver.add(meeting_start >= 12*30)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time_minutes = model[meeting_start].as_long()
    start_hour = start_time_minutes // 60
    start_minute = start_time_minutes % 60
    end_hour = (start_time_minutes + meeting_duration) // 60
    end_minute = (start_time_minutes + meeting_duration) % 60
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")