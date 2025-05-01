from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for the problem
arrival_time = 9 * 60  # Arrival at Richmond District at 9:00 AM (in minutes)
travel_time_to_financial = 22  # Travel time from Richmond District to Financial District
travel_time_back = 21  # Travel time from Financial District to Richmond District

# Betty's availability
betty_start = 17 * 60 + 15  # 5:15 PM in minutes
betty_end = 21 * 60 + 45    # 9:45 PM in minutes
meeting_duration = 60        # Minimum meeting duration in minutes

# Define the time when you can start the meeting
meeting_start = Int('meeting_start')

# Constraints for the meeting time
s.add(meeting_start >= arrival_time + travel_time_to_financial)  # Must arrive at Financial District after travel
s.add(meeting_start >= betty_start)                              # Must arrive after Betty's availability starts
s.add(meeting_start + meeting_duration <= betty_end)            # Must leave before Betty's availability ends

# Add a constraint to ensure you have enough time to return after the meeting
s.add(meeting_start + meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + meeting_duration  # Calculate when you leave the meeting

    print("Trip plan is possible with the following details:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")

else:
    print("No possible trip plan found.")