from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel
travel_time_to_nob_hill = 11  # Travel time from Fisherman's Wharf to Nob Hill (in minutes)
travel_time_back = 11          # Travel time from Nob Hill back to Fisherman's Wharf (in minutes)

# Constants for timing
arrival_time = 9 * 60         # Arrival at Fisherman's Wharf at 9:00 AM (in minutes)
kenneth_start = 14 * 60 + 15  # Kenneth is at Nob Hill starting at 2:15 PM (in minutes)
kenneth_end = 19 * 60 + 45    # Kenneth leaves Nob Hill at 7:45 PM (in minutes)
min_meeting_duration = 90      # Minimum meeting duration in minutes

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_nob_hill)  # Must arrive at Nob Hill after travel
s.add(meeting_start >= kenneth_start)                            # Must meet after Kenneth is available
s.add(meeting_start + min_meeting_duration <= kenneth_end)      # Meeting must finish before Kenneth leaves

# Add a constraint to ensure you have enough time to return after the meeting
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you leave the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")