from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_union_square = 9  # Travel time from Financial District to Union Square (in minutes)
travel_time_back = 9               # Travel time from Union Square back to Financial District (in minutes)

# Constants for timing
arrival_time = 9 * 60              # Arrival at Financial District at 9:00 AM (540 minutes)
joseph_start = 21 * 60 + 30        # Joseph will be at Union Square from 9:30 PM (1290 minutes)
joseph_end = 22 * 60               # Joseph leaves at 10:00 PM (1200 minutes)
min_meeting_duration = 15           # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_union_square)  # Must arrive at Union Square after traveling
s.add(meeting_start >= joseph_start)                                 # Meeting must start after Joseph arrives
s.add(meeting_start + min_meeting_duration <= joseph_end)           # Meeting must finish before Joseph leaves

# Add a constraint to ensure there's enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate the end time of the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time to HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time to HH:MM
else:
    print("No possible trip plan found.")