from z3 import *

# Define the time in minutes from 00:00 to 23:59
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02}:{minutes:02}"

# Define the travel times
travel_times = {
    ('Chinatown', 'Mission District'): 18,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Presidio'): 19,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Pacific Heights'): 16,
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
    ('Union Square', 'Pacific Heights'): 15,
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
    ('Presidio', 'Sunset District'): 15,
}

# Define the friends and their availability
friends = {
    'David': ('Mission District', time_to_minutes('08:00'), time_to_minutes('19:45'), 45),
    'Kenneth': ('Alamo Square', time_to_minutes('14:00'), time_to_minutes('19:45'), 120),
    'John': ('Pacific Heights', time_to_minutes('17:00'), time_to_minutes('20:00'), 15),
    'Charles': ('Union Square', time_to_minutes('21:45'), time_to_minutes('22:45'), 60),
    'Deborah': ('Golden Gate Park', time_to_minutes('07:00'), time_to_minutes('18:15'), 90),
    'Karen': ('Sunset District', time_to_minutes('17:45'), time_to_minutes('21:15'), 15),
    'Carol': ('Presidio', time_to_minutes('08:15'), time_to_minutes('09:15'), 30),
}

# Define the solver
solver = Solver()

# Define the variables
current_location = 'Chinatown'
current_time = Int('current_time')
solver.add(current_time == time_to_minutes('09:00'))

# Define the meeting variables and constraints
meetings = {}
locations = [current_location]
times = [current_time]

for i, (friend, (location, start, end, duration)) in enumerate(friends.items()):
    meet_start = Int(f'meet_start_{friend}')
    meet_end = Int(f'meet_end_{friend}')
    meetings[friend] = (meet_start, meet_end)
    
    # Constraints for meeting with the friend
    solver.add(meet_start >= start)
    solver.add(meet_end <= end)
    solver.add(meet_end - meet_start >= duration)
    
    # Constraints for traveling to the friend's location
    travel_time = Int(f'travel_time_{friend}')
    solver.add(travel_time == travel_times[(locations[-1], location)])
    solver.add(meet_start == times[-1] + travel_time)
    
    # Update current location and time after meeting
    locations.append(location)
    times.append(meet_end)

# Define the objective to maximize the number of meetings
objective = Optimize()
objective.add(solver.assertions())
objective.maximize(Sum([If(meetings[friend][1] - meetings[friend][0] > 0, 1, 0) for friend in friends]))

# Solve the problem
if objective.check() == sat:
    model = objective.model()
    itinerary = []
    current_time = time_to_minutes('09:00')
    current_location = 'Chinatown'
    
    for friend, (start, end) in meetings.items():
        meet_start = model.evaluate(start).as_long()
        meet_end = model.evaluate(end).as_long()
        if meet_end - meet_start > 0:
            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": minutes_to_time(meet_start),
                "end_time": minutes_to_time(meet_end)
            })
            current_time = meet_end
            current_location = friends[friend][0]
    
    print({"itinerary": itinerary})
else:
    print("No solution found")