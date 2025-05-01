from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_pacific_heights = 7  # Travel time from Marina District to Pacific Heights (in minutes)
travel_time_back = 6                  # Travel time from Pacific Heights back to Marina District (in minutes)

# Constants for timing
arrival_time = 9 * 60                # Arrival at Marina District at 9:00 AM (540 minutes)
margaret_start = 19 * 60             # Margaret is at Pacific Heights starting at 7:00 PM (1140 minutes)
margaret_end = 19 * 60 + 45          # Margaret leaves at 7:45 PM (1185 minutes)
min_meeting_duration = 15             # Minimum meeting duration in minutes

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_pacific_heights)  # Must arrive at Pacific Heights after traveling
s.add(meeting_start >= margaret_start)                                   # Meeting must start after Margaret is available
s.add(meeting_start + min_meeting_duration <= margaret_end)             # Meeting must finish before Margaret leaves

# Add a constraint to ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when the meeting will end

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")