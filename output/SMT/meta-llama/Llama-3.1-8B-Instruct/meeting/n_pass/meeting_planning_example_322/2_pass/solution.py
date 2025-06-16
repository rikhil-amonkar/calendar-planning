from z3 import *

# Define the travel times
travel_times = {
    'Sunset District to Russian Hill': 24,
    'Sunset District to Chinatown': 30,
    'Sunset District to Presidio': 16,
    'Sunset District to Fisherman\'s Wharf': 29,
    'Russian Hill to Sunset District': 23,
    'Russian Hill to Chinatown': 9,
    'Russian Hill to Presidio': 14,
    'Russian Hill to Fisherman\'s Wharf': 7,
    'Chinatown to Sunset District': 29,
    'Chinatown to Russian Hill': 7,
    'Chinatown to Presidio': 19,
    'Chinatown to Fisherman\'s Wharf': 8,
    'Presidio to Sunset District': 15,
    'Presidio to Russian Hill': 14,
    'Presidio to Chinatown': 21,
    'Presidio to Fisherman\'s Wharf': 19,
    'Fisherman\'s Wharf to Sunset District': 27,
    'Fisherman\'s Wharf to Russian Hill': 7,
    'Fisherman\'s Wharf to Chinatown': 12,
    'Fisherman\'s Wharf to Presidio': 17
}

# Define the constraints
s = Optimize()
time = 540  # Total time in minutes
meetings = []

# William
william_start = 390  # 6:30 PM
william_end = 465  # 8:45 PM
william_duration = 105  # Minimum meeting duration
meetings.append(('William', william_start, william_end, william_duration))

# Michelle
michelle_start = 0  # 8:15 AM
michelle_end = 120  # 2:00 PM
michelle_duration = 15  # Minimum meeting duration
meetings.append(('Michelle', michelle_start, michelle_end, michelle_duration))

# George
george_start = 30  # 10:30 AM
george_end = 405  # 6:45 PM
george_duration = 30  # Minimum meeting duration
meetings.append(('George', george_start, george_end, george_duration))

# Robert
robert_start = 0  # 9:00 AM
robert_end = 105  # 1:45 PM
robert_duration = 30  # Minimum meeting duration
meetings.append(('Robert', robert_start, robert_end, robert_duration))

# Define the variables
x = [Bool(f'x_{i}') for i in range(len(meetings))]

# Define the constraints
for i in range(len(meetings)):
    name, start, end, duration = meetings[i]
    s.add(If(x[i], start + duration, 0) >= 0)
    s.add(x[i] <= If(end <= time, end, time))

# Define the objective function
s.set_objective(Sum([x[i] * (end - start) for i, (name, start, end, duration) in enumerate(meetings) if x[i]]),'max')

# Solve the problem
s.solve()

# Print the solution
if s.model():
    solution = [s.model()[f'x_{i}'] for i in range(len(meetings))]
    print("SOLUTION:")
    for i in range(len(meetings)):
        name, start, end, duration = meetings[i]
        if solution[i].as_bool().value():
            print(f"Meet {name} from {start} to {end} for {duration} minutes")
else:
    print("No solution found")