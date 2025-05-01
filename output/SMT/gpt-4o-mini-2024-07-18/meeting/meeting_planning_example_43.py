from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_chinatown = 16  # Travel time from Marina District to Chinatown (in minutes)
travel_time_back = 12           # Travel time from Chinatown back to Marina District (in minutes)

# Constants for timing
arrival_time = 9 * 60          # Arrival at Marina District at 9:00 AM (540 minutes)
sandra_start = 9 * 60          # Sandra will be at Chinatown starting at 9:00 AM (540 minutes)
sandra_end = 11 * 60 + 45      # Sandra leaves at 11:45 AM (705 minutes)
min_meeting_duration = 15       # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_chinatown)  # Must arrive at Chinatown after traveling
s.add(meeting_start >= sandra_start)                             # Meeting must start after Sandra is available
s.add(meeting_start + min_meeting_duration <= sandra_end)       # Meeting must finish before Sandra leaves

# Add a constraint to ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate end time of the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time to HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time to HH:MM
else:
    print("No possible trip plan found.")