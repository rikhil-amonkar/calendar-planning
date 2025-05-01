from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_bayview = 31  # Travel time from Presidio to Bayview (in minutes)
travel_time_back = 31         # Travel time from Bayview back to Presidio (in minutes)

# Constants for timing
arrival_time = 9 * 60              # Arrival at Presidio at 9:00AM (540 minutes)
nancy_start = 7 * 60 + 15          # Nancy will be at Bayview from 7:15AM (435 minutes)
nancy_end = 17 * 60 + 30           # Nancy leaves at 5:30PM (1050 minutes)
min_meeting_duration = 30           # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_bayview)  # Must arrive at Bayview after traveling
s.add(meeting_start >= nancy_start)                            # Meeting must start after Nancy is available
s.add(meeting_start + min_meeting_duration <= nancy_end)      # Meeting must finish before Nancy leaves

# Add a constraint to ensure there is enough time to return after the meeting is over
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