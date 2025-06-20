from z3 import *

# Define the variables
start_time = 9 * 60  # 9:00 AM in minutes
betty_arrival, betty_departure = 10 * 60 + 15, 21 * 60  # Betty's arrival and departure times in minutes
david_arrival, david_departure = 1 * 60, 8 * 60 + 15  # David's arrival and departure times in minutes
barbara_arrival, barbara_departure = 9 * 60 + 15, 8 * 60 + 15  # Barbara's arrival and departure times in minutes

# Define the meeting durations
min_meeting_duration_betty = 45  # Minimum meeting duration with Betty in minutes
min_meeting_duration_david = 90  # Minimum meeting duration with David in minutes
min_meeting_duration_barbara = 120  # Minimum meeting duration with Barbara in minutes

# Define the travel times
travel_times = {
    'Embarcadero': {'Presidio': 20, 'Richmond District': 21, 'Fisherman\'s Wharf': 6},
    'Presidio': {'Embarcadero': 20, 'Richmond District': 7, 'Fisherman\'s Wharf': 19},
    'Richmond District': {'Embarcadero': 19, 'Presidio': 7, 'Fisherman\'s Wharf': 18},
    'Fisherman\'s Wharf': {'Embarcadero': 8, 'Presidio': 17, 'Richmond District': 18}
}

# Define the solver
s = Solver()

# Define the variables for the meeting times
betty_meeting_time = Int('betty_meeting_time')
david_meeting_time = Int('david_meeting_time')
barbara_meeting_time = Int('barbara_meeting_time')

# Define the constraints
s.add(betty_meeting_time >= betty_arrival)
s.add(betty_meeting_time + min_meeting_duration_betty <= betty_departure)
s.add(david_meeting_time >= david_arrival)
s.add(david_meeting_time + min_meeting_duration_david <= david_departure)
s.add(barbara_meeting_time >= barbara_arrival)
s.add(barbara_meeting_time + min_meeting_duration_barbara <= barbara_departure)

# Define the constraints for the travel times
s.add(betty_meeting_time >= start_time + travel_times['Embarcadero']['Presidio'])
s.add(david_meeting_time >= start_time + travel_times['Embarcadero']['Richmond District'])
s.add(barbara_meeting_time >= start_time + travel_times['Embarcadero']['Fisherman\'s Wharf'])

# Define the constraints for the meeting times
s.add(betty_meeting_time <= david_meeting_time - min_meeting_duration_david)
s.add(betty_meeting_time <= barbara_meeting_time - min_meeting_duration_barbara)
s.add(david_meeting_time <= barbara_meeting_time - min_meeting_duration_barbara)

# Solve the problem
s.check()
model = s.model()

# Print the solution
print("SOLUTION:")
print(f"Meet Betty at {model[betty_meeting_time].as_long() / 60} hours")
print(f"Meet David at {model[david_meeting_time].as_long() / 60} hours")
print(f"Meet Barbara at {model[barbara_meeting_time].as_long() / 60} hours")