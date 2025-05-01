from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times and timing
travel_time_to_embarcadero = 22  # Travel time from The Castro to Embarcadero (in minutes)
travel_time_back = 25              # Travel time from Embarcadero back to The Castro (in minutes)

# Constants for timing
arrival_time = 9 * 60              # Arrival at The Castro at 9:00 AM (540 minutes)
laura_start = 8 * 60               # Laura is at Embarcadero starting at 8:00 AM (480 minutes)
laura_end = 11 * 60                # Laura leaves at 11:00 AM (660 minutes)
min_meeting_duration = 15           # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_embarcadero)  # Must arrive at Embarcadero after traveling
s.add(meeting_start >= laura_start)                                # Meeting must start after Laura is available
s.add(meeting_start + min_meeting_duration <= laura_end)          # Meeting must finish before Laura leaves

# Add a constraint to ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate the end time of the meeting.

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time to HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time to HH:MM
else:
    print("No possible trip plan found.")