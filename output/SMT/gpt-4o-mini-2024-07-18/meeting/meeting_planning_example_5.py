from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for the problem
arrival_time = 9 * 60  # Arrival at Nob Hill at 9:00 AM (in minutes)
travel_time_to_castro = 17  # Travel time from Nob Hill to The Castro (in minutes)
travel_time_back = 16        # Travel time from The Castro to Nob Hill (in minutes)

# William's availability
william_start = 12 * 60 + 15  # 12:15 PM in minutes
william_end = 22 * 60          # 10:00 PM in minutes
min_meeting_duration = 75       # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for the meeting time
s.add(meeting_start >= arrival_time + travel_time_to_castro)  # Must arrive at The Castro after travelling
s.add(meeting_start >= william_start)                          # Meeting must start after William is available
s.add(meeting_start + min_meeting_duration <= william_end)    # Meeting must finish before William leaves

# Add a constraint to ensure you have time to return after the meeting
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