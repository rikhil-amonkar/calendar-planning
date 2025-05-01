from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_alamo = 13  # Travel time from Richmond District to Alamo Square (in minutes)
travel_time_back = 12       # Travel time from Alamo Square back to Richmond District (in minutes)

# Constants for timing
arrival_time = 9 * 60         # Arrival at Richmond District at 9:00 AM (540 minutes)
betty_start = 12 * 60 + 30    # Betty will be at Alamo Square from 12:30 PM (750 minutes)
betty_end = 19 * 60 + 15      # Betty leaves at 7:15 PM (1155 minutes)
min_meeting_duration = 75      # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_alamo)  # Must arrive at Alamo Square after traveling
s.add(meeting_start >= betty_start)                           # Meeting must start after Betty is available
s.add(meeting_start + min_meeting_duration <= betty_end)     # Meeting must finish before Betty leaves

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