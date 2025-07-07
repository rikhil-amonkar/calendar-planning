from z3 import *

# Define the locations
locations = ['The Castro', 'Bayview', 'Pacific Heights', 'Alamo Square', 'Fisherman\'s Wharf', 'Golden Gate Park']

# Define the travel times in minutes
travel_times = {
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Bayview', 'The Castro'): 20,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Fisherman\'s Wharf', 'The Castro'): 26,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Alamo Square'): 20,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
}

# Define the friends' availability
availability = {
    'Rebecca': ('Bayview', 9*60, 12*60 + 45),  # 9:00AM to 12:45PM
    'Amanda': ('Pacific Heights', 18*60 + 30, 21*60 + 45),  # 6:30PM to 9:45PM
    'James': ('Alamo Square', 9*60 + 45, 21*60 + 15),  # 9:45AM to 9:15PM
    'Sarah': ('Fisherman\'s Wharf', 8*60, 21*60 + 30),  # 8:00AM to 9:30PM
    'Melissa': ('Golden Gate Park', 9*60, 18*60 + 45)  # 9:00AM to 6:45PM
}

# Define the minimum meeting time in minutes
min_meeting_time = 90

# Create a solver instance
solver = Solver()

# Define variables for the schedule
visit_times = {friend: Int(f'{friend}_visit_time') for friend in availability}
location_vars = {friend: String(f'{friend}_location') for friend in availability}

# Add constraints for each friend
for friend, (loc, start, end) in availability.items():
    solver.add(location_vars[friend] == loc)
    solver.add(visit_times[friend] >= start)
    solver.add(visit_times[friend] + min_meeting_time <= end)

# Add constraints for travel times
current_location = 'The Castro'
current_time = 9 * 60  # 9:00AM

for friend, (loc, start, end) in availability.items():
    travel_time = travel_times[(current_location, loc)]
    current_time += travel_time
    solver.add(visit_times[friend] >= current_time)
    current_location = loc
    current_time += min_meeting_time

# Optimize the schedule
if solver.check() == sat:
    model = solver.model()
    schedule = [(friend, model[visit_times[friend]].as_long(), model[location_vars[friend]].as_string()) for friend in availability]
    schedule.sort(key=lambda x: x[1])
    print("SOLUTION:")
    for friend, visit_time, location in schedule:
        print(f"{friend}: {location} at {visit_time // 60}:{visit_time % 60:02d}")
else:
    print("No solution found")