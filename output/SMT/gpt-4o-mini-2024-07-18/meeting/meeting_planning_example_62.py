from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_russian_hill = 14  # Travel time from Presidio to Russian Hill (in minutes)
travel_time_back = 14               # Travel time from Russian Hill back to Presidio (in minutes)

# Constants for timing
arrival_time = 9 * 60              # Arrival at Presidio at 9:00 AM (540 minutes)
amanda_start = 11 * 60 + 30        # Amanda will be at Russian Hill from 11:30 AM (690 minutes)
amanda_end = 21 * 60 + 15          # Amanda leaves at 9:15 PM (1115 minutes)
min_meeting_duration = 15           # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_russian_hill)  # Must arrive at Russian Hill after traveling
s.add(meeting_start >= amanda_start)                                   # Meeting must start after Amanda is available
s.add(meeting_start + min_meeting_duration <= amanda_end)            # Meeting must finish before Amanda leaves

# Add a constraint to ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate end time of the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time as HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time as HH:MM
else:
    print("No possible trip plan found.")