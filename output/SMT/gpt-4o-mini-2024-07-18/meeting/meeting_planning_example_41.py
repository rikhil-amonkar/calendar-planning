from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constant travel times
travel_time_to_haight = 18  # Travel time from North Beach to Haight-Ashbury
travel_time_back = 19        # Travel time from Haight-Ashbury back to North Beach

# Constants for timing
arrival_time = 9 * 60         # Arrival at North Beach at 9:00 AM (540 minutes)
george_start = 7 * 60 + 30    # George is at Haight-Ashbury starting at 7:30 AM (450 minutes)
george_end = 13 * 60 + 15      # George leaves at 1:15 PM (795 minutes)
min_meeting_duration = 45      # Minimum meeting duration in minutes

# Define a variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for the meeting time
s.add(meeting_start >= arrival_time + travel_time_to_haight)  # Must arrive at Haight-Ashbury after traveling
s.add(meeting_start >= george_start)                           # Must start meeting after George arrives
s.add(meeting_start + min_meeting_duration <= george_end)     # Must finish meeting before George leaves

# Add a constraint to ensure there is enough time to return after the meeting
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you will finish the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")