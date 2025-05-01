from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_union_square = 13  # Travel time from Fisherman's Wharf to Union Square (in minutes)
travel_time_back = 15               # Travel time from Union Square back to Fisherman's Wharf (in minutes)

# Constants for timing
arrival_time = 9 * 60              # Arrival at Fisherman's Wharf at 9:00 AM (540 minutes)
kevin_start = 13 * 60 + 15         # Kevin will be at Union Square from 1:15 PM (795 minutes)
kevin_end = 19 * 60 + 15           # Kevin leaves at 7:15 PM (1115 minutes)
min_meeting_duration = 15           # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_union_square)  # Must arrive at Union Square after traveling
s.add(meeting_start >= kevin_start)                                  # Meeting must start after Kevin is available
s.add(meeting_start + min_meeting_duration <= kevin_end)            # Meeting must finish before Kevin leaves

# Ensure there's enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when the meeting will end

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time as HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time as HH:MM
else:
    print("No possible trip plan found.")