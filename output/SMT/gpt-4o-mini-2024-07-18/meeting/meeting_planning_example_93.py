from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_chinatown = 6  # Travel time from North Beach to Chinatown (in minutes)
travel_time_back = 3           # Travel time from Chinatown back to North Beach (in minutes)

# Constants for timing
arrival_time = 9 * 60          # Arrival at North Beach at 9:00 AM (540 minutes)
emily_start = 19 * 60          # Emily will be at Chinatown from 7:00 PM (1140 minutes)
emily_end = 21 * 60            # Emily leaves at 9:00 PM (1260 minutes)
min_meeting_duration = 75       # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_chinatown)  # Must arrive at Chinatown after traveling
s.add(meeting_start >= emily_start)                              # Meeting must start after Emily is available
s.add(meeting_start + min_meeting_duration <= emily_end)        # Meeting must finish before Emily leaves

# Add a constraint to ensure you have enough time to return after the meeting
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you finish the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time as HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time as HH:MM
else:
    print("No possible trip plan found.")