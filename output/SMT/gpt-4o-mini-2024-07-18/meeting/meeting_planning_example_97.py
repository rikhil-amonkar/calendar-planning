from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_richmond = 20  # Travel time from Chinatown to Richmond District (in minutes)
travel_time_back = 20          # Travel time from Richmond District back to Chinatown (in minutes)

# Constants for timing
arrival_time = 9 * 60          # Arrival at Chinatown at 9:00 AM (540 minutes)
charles_start = 18 * 60        # Charles will be at Richmond District from 6:00 PM (1080 minutes)
charles_end = 21 * 60          # Charles leaves at 9:00 PM (1260 minutes)
min_meeting_duration = 75       # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_richmond)  # Must arrive at Richmond District after traveling
s.add(meeting_start >= charles_start)                            # Meeting must start after Charles is available
s.add(meeting_start + min_meeting_duration <= charles_end)      # Meeting must finish before Charles leaves

# Ensure there is enough time to return after the meeting is over
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