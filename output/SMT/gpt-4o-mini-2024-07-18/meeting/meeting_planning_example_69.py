from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_union_square = 7  # Travel time from Chinatown to Union Square (in minutes)
travel_time_back = 7               # Travel time from Union Square back to Chinatown (in minutes)

# Constants for timing
arrival_time = 9 * 60              # Arrival at Chinatown at 9:00 AM (540 minutes)
mark_start = 8 * 60                # Mark is at Union Square from 8:00 AM (480 minutes)
mark_end = 12 * 60 + 45            # Mark leaves at 12:45 PM (765 minutes)
min_meeting_duration = 90           # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_union_square)  # Must arrive at Union Square after traveling
s.add(meeting_start >= mark_start)                                   # Meeting must start after Mark is available
s.add(meeting_start + min_meeting_duration <= mark_end)             # Meeting must finish before Mark leaves

# Ensure there is enough time to return after the meeting
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you finish the meeting.

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time as HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time as HH:MM
else:
    print("No possible trip plan found.")