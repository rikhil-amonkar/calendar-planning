from z3 import *

# Define the travel times between locations
travel_times = {
    ('Chinatown', 'Mission District'): 16,
    ('Chinatown', 'Alamo Square'): 16,
    ('Chinatown', 'Pacific Heights'): 11,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Presidio'): 19,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Alamo Square'): 10,
    ('Mission District', 'Pacific Heights'): 15,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Presidio'): 25,
    ('Alamo Square', 'Chinatown'): 16,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Presidio'): 18,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Presidio'): 11,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Pacific Heights'): 12,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Sunset District'): 26,
    ('Union Square', 'Presidio'): 24,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Presidio'): 16,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Alamo Square'): 18,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Sunset District'): 15
}

# Define the constraints
s = Solver()

# Define the variables
locations = ['Chinatown', 'Mission District', 'Alamo Square', 'Pacific Heights', 'Union Square', 'Golden Gate Park', 'Sunset District', 'Presidio']
times = [9]  # initial time
visits = [Bool('v_' + location) for location in locations]
durations = [Int('d_' + location) for location in locations]

# Add constraints for each person
s.add(Or(visits['Mission District'], And(visits['Mission District'], And(times[-1] >= 8, times[-1] <= 7.75, durations['Mission District'] >= 45))))
s.add(Or(visits['Alamo Square'], And(visits['Alamo Square'], And(times[-1] >= 2, times[-1] <= 7.75, durations['Alamo Square'] >= 120))))
s.add(Or(visits['Pacific Heights'], And(visits['Pacific Heights'], And(times[-1] >= 5, times[-1] <= 8, durations['Pacific Heights'] >= 15))))
s.add(Or(visits['Union Square'], And(visits['Union Square'], And(times[-1] >= 9.75, times[-1] <= 10.75, durations['Union Square'] >= 60))))
s.add(Or(visits['Golden Gate Park'], And(visits['Golden Gate Park'], And(times[-1] >= 7, times[-1] <= 6.25, durations['Golden Gate Park'] >= 90))))
s.add(Or(visits['Sunset District'], And(visits['Sunset District'], And(times[-1] >= 5.75, times[-1] <= 9.25, durations['Sunset District'] >= 15))))
s.add(Or(visits['Presidio'], And(visits['Presidio'], And(times[-1] >= 8.25, times[-1] <= 9.25, durations['Presidio'] >= 30))))

# Add constraints for travel times
for i in range(len(locations)):
    for j in range(i+1, len(locations)):
        s.add(Implies(visits[locations[i]], And(visits[locations[j]], times[-1] + travel_times[(locations[i], locations[j])] >= times[i+1])))

# Add constraints for time ordering
for i in range(len(locations) - 1):
    s.add(times[i+1] >= times[i] + durations[locations[i]])

# Add constraints for initial time
s.add(times[0] == 9)

# Solve the problem
s.check()
model = s.model()

# Print the solution
print("SOLUTION:")
for location in locations:
    if model.evaluate(visits[location]):
        print(f"Visit {location} for {model.evaluate(durations[location])} minutes at {model.evaluate(times[locations.index(location)])} hours")

# Print the order of visits
print("\nOrder of visits:")
for i in range(len(locations)):
    print(f"{locations[i]}: {model.evaluate(times[i])} hours")