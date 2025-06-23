from z3 import *

# Define the variables
start_time = Int('start_time')
end_time = Int('end_time')
barbara_start_time = Int('barbara_start_time')
barbara_end_time = Int('barbara_end_time')
meeting_duration = Int('meeting_duration')
max_meetings = Int('max_meetings')

# Define the constraints
s = Optimize()
s.add(start_time >= 0)  # Start time should be non-negative
s.add(end_time >= 0)  # End time should be non-negative
s.add(barbara_start_time == 1*60 + 15)  # Barbara starts at 1:15 PM
s.add(barbara_end_time == 6*60 + 15)  # Barbara ends at 6:15 PM
s.add(meeting_duration >= 45)  # Meeting duration should be at least 45 minutes

# Define the possible meeting times
possible_meeting_times = []
for i in range(9*60, 18*60):
    possible_meeting_times.append(i)

# Define the objective function
max_meetings = s.int_const('max_meetings')
s.add(If(meeting_duration >= 45, max_meetings, 0) >= 0)
s.maximize(max_meetings)  # Maximize the number of friends met

# Define the constraints for each possible meeting time
for i in possible_meeting_times:
    s.add(If(i >= barbara_start_time - 45 - 13, meeting_duration + 1, 0) >= 0)

# Solve the problem
s.check()
model = s.model()

# Print the optimal schedule
print("Optimal schedule:")
print(f"Start time: {model[start_time]} minutes past 9:00 AM")
print(f"End time: {model[end_time]} minutes past 9:00 AM")
print(f"Meeting duration: {model[meeting_duration]} minutes")
print(f"Number of friends met: {model[max_meetings]}")