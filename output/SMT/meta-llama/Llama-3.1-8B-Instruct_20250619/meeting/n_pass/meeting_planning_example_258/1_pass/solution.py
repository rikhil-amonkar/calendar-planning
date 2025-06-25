from z3 import *

# Define the travel distances
distances = {
    'Embarcadero': {'Presidio': 20, 'Richmond District': 21, 'Fisherman\'s Wharf': 6},
    'Presidio': {'Embarcadero': 20, 'Richmond District': 7, 'Fisherman\'s Wharf': 19},
    'Richmond District': {'Embarcadero': 19, 'Presidio': 7, 'Fisherman\'s Wharf': 18},
    'Fisherman\'s Wharf': {'Embarcadero': 8, 'Presidio': 17, 'Richmond District': 18}
}

# Define the meeting constraints
betty_start, betty_end = 10 * 60, 9 * 60 * 16  # 10:15AM to 9:30PM
betty_duration = 45 * 60

david_start, david_end = 1 * 60, 8 * 60 * 16  # 1:00PM to 8:15PM
david_duration = 90 * 60

barbara_start, barbara_end = 9 * 60, 8 * 60 * 16  # 9:15AM to 8:15PM
barbara_duration = 120 * 60

# Define the variables
s = Solver()

locations = ['Embarcadero', 'Presidio', 'Richmond District', 'Fisherman\'s Wharf']
times = []
for location in locations:
    for time in range(betty_start, betty_end + 1):
        times.append((location, time))

meeting_times = [Int(f'meeting_time_{i}') for i in range(len(times))]

# Define the constraints
for i, (location, time) in enumerate(times):
    s.add(meeting_times[i] >= time)
    s.add(meeting_times[i] <= betty_end if location == 'Presidio' else david_end if location == 'Richmond District' else barbara_end)
    s.add(meeting_times[i] >= betty_start if location == 'Presidio' else david_start if location == 'Richmond District' else barbara_start)
    s.add(meeting_times[i] + barbara_duration <= barbara_end if location == 'Fisherman\'s Wharf' else meeting_times[i] + david_duration <= david_end if location == 'Richmond District' else meeting_times[i] + betty_duration <= betty_end)
    s.add(meeting_times[i] + distances[location]['Embarcadero'] <= time + 60 if location == 'Presidio' else meeting_times[i] + distances[location]['Embarcadero'] <= time + 60 if location == 'Richmond District' else meeting_times[i] + distances[location]['Embarcadero'] <= time + 60)

# Solve the problem
s.check()

model = s.model()

# Print the optimal schedule
optimal_schedule = []
for i, (location, time) in enumerate(times):
    if model[meeting_times[i]].as_long() >= time and model[meeting_times[i]].as_long() <= betty_end if location == 'Presidio' else model[meeting_times[i]].as_long() >= david_start and model[meeting_times[i]].as_long() <= david_end if location == 'Richmond District' else model[meeting_times[i]].as_long() >= barbara_start and model[meeting_times[i]].as_long() <= barbara_end:
        optimal_schedule.append((location, model[meeting_times[i]].as_long()))

optimal_schedule.sort(key=lambda x: x[1])
for location, time in optimal_schedule:
    print(f'Visit {location} at {time // 60}:{(time % 60):02d}')

print(f'\nTotal duration: {(max(optimal_schedule, key=lambda x: x[1])[1] - 9 * 60) // 60}:{((max(optimal_schedule, key=lambda x: x[1])[1] - 9 * 60) % 60):02d}')