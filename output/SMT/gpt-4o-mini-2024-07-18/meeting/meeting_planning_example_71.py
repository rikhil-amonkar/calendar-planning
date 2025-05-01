from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_bayview = 18  # Travel time from Haight-Ashbury to Bayview (in minutes)
travel_time_back = 19         # Travel time from Bayview back to Haight-Ashbury (in minutes)

# Constants for timing
arrival_time = 9 * 60         # Arrival at Haight-Ashbury at 9:00 AM (540 minutes)
paul_start = 11 * 60          # Paul will be at Bayview from 11:00 AM (660 minutes)
paul_end = 16 * 60 + 30       # Paul leaves Bayview at 4:30 PM (990 minutes)
min_meeting_duration = 90      # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_bayview)  # Must arrive at Bayview after traveling
s.add(meeting_start >= paul_start)                             # Meeting must start after Paul is available
s.add(meeting_start + min_meeting_duration <= paul_end)       # Meeting must finish before Paul leaves

# Ensure enough time to return after the meeting
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate ending time for the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time to HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time to HH:MM
else:
    print("No possible trip plan found.")