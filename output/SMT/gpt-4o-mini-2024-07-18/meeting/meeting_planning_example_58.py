from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_financial = 20  # Travel time from The Castro to Financial District (in minutes)
travel_time_back = 23            # Travel time from Financial District back to The Castro (in minutes)

# Constants for timing
arrival_time = 9 * 60           # Arrival at The Castro at 9:00 AM (540 minutes)
nancy_start = 9 * 60 + 15       # Nancy is at Financial District from 9:15 AM (555 minutes)
nancy_end = 16 * 60 + 45        # Nancy leaves at 4:45 PM (1005 minutes)
min_meeting_duration = 30        # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_financial)  # Must arrive after traveling
s.add(meeting_start >= nancy_start)                              # Meeting must start after Nancy arrives
s.add(meeting_start + min_meeting_duration <= nancy_end)        # Meeting must finish before Nancy leaves

# Ensure there is enough time to return after the meeting
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when the meeting ends.

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time as HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time as HH:MM
else:
    print("No possible trip plan found.")