from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel and timing
arrival_time = 9 * 60  # Arrival at Union Square at 9:00 AM in minutes
travel_time_to_nob_hill = 9  # Travel time from Union Square to Nob Hill (in minutes)
travel_time_back = 7           # Travel time from Nob Hill back to Union Square (in minutes)

# Mary's availability
mary_start = 12 * 60  # Mary is at Nob Hill starting at 12:00 PM (720 minutes)
mary_end = 16 * 60 + 15  # Mary leaves at 4:15 PM (975 minutes)
min_meeting_duration = 75  # Minimum meeting duration in minutes

# Define variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_nob_hill)  # Must arrive at Nob Hill after travel
s.add(meeting_start >= mary_start)                              # Must arrive after Mary is available
s.add(meeting_start + min_meeting_duration <= mary_end)        # Must finish meeting before Mary leaves

# Ensure there is enough time to return to Union Square after the meeting
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