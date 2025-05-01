from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times and other timing
arrival_time = 9 * 60  # Arrival at Sunset District at 9:00 AM (540 minutes)
travel_time_to_haight = 15  # Travel time from Sunset District to Haight-Ashbury (in minutes)
travel_time_back = 15        # Travel time from Haight-Ashbury back to Sunset District (in minutes)

# Nancy's availability
nancy_start = 19 * 60 + 30  # Nancy will be at Haight-Ashbury starting at 7:30 PM (1170 minutes)
nancy_end = 21 * 60 + 45     # Nancy leaves at 9:45 PM (1305 minutes)
min_meeting_duration = 75     # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_haight)  # Must arrive at Haight-Ashbury after travelling
s.add(meeting_start >= nancy_start)                            # Meeting must start after Nancy is available
s.add(meeting_start + min_meeting_duration <= nancy_end)      # Meeting must finish before Nancy leaves

# Add a constraint to ensure you have enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate the end time of the meeting.

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")