from z3 import *

# Define the variables
time_slots = [
    '9:00-10:00', '10:00-11:00', '11:00-11:45', '11:45-12:45', '12:45-2:30',
    '2:30-4:15', '4:15-5:30', '5:30-6:45', '6:45-7:15', '7:15-9:30'
]
num_time_slots = len(time_slots)
friends = ['Andrew', 'Sarah', 'Nancy', 'Rebecca', 'Robert']
locations = ['Union Square', 'Golden Gate Park', 'Pacific Heights', 'Presidio', 'Chinatown', 'The Castro']

# Define the travel times
travel_times = {
    'Union Square': {'Golden Gate Park': 22, 'Pacific Heights': 15, 'Presidio': 24, 'Chinatown': 7, 'The Castro': 19},
    'Golden Gate Park': {'Union Square': 22, 'Pacific Heights': 16, 'Presidio': 11, 'Chinatown': 23, 'The Castro': 13},
    'Pacific Heights': {'Union Square': 12, 'Golden Gate Park': 15, 'Presidio': 11, 'Chinatown': 11, 'The Castro': 16},
    'Presidio': {'Union Square': 22, 'Golden Gate Park': 12, 'Pacific Heights': 11, 'Chinatown': 21, 'The Castro': 21},
    'Chinatown': {'Union Square': 7, 'Golden Gate Park': 23, 'Pacific Heights': 10, 'Presidio': 19, 'The Castro': 22},
    'The Castro': {'Union Square': 19, 'Golden Gate Park': 11, 'Pacific Heights': 16, 'Presidio': 20, 'Chinatown': 20}
}

# Define the constraints
s = Optimize()
x = [Bool(f'{friend}_{location}') for friend in friends for location in locations]

# Meet Andrew for at least 75 minutes
andrew_meeting = 0
for i in range(num_time_slots):
    if time_slots[i] == '11:45-12:45' or time_slots[i] == '11:45-2:30':
        andrew_meeting += If(x[friends.index('Andrew')*6 + locations.index('Golden Gate Park')], 75, 0)
    else:
        andrew_meeting += 0
s.add(andrew_meeting >= 75)

# Meet Sarah for at least 15 minutes
sarah_meeting = 0
for i in range(num_time_slots):
    if time_slots[i] == '4:15-5:30' or time_slots[i] == '4:15-6:45':
        sarah_meeting += If(x[friends.index('Sarah')*6 + locations.index('Pacific Heights')], 15, 0)
    else:
        sarah_meeting += 0
s.add(sarah_meeting >= 15)

# Meet Nancy for at least 60 minutes
nancy_meeting = 0
for i in range(num_time_slots):
    if time_slots[i] == '5:30-6:45' or time_slots[i] == '5:30-7:15':
        nancy_meeting += If(x[friends.index('Nancy')*6 + locations.index('Presidio')], 60, 0)
    else:
        nancy_meeting += 0
s.add(nancy_meeting >= 60)

# Meet Rebecca for at least 90 minutes
rebecca_meeting = 0
for i in range(num_time_slots):
    if time_slots[i] == '9:00-10:00' or time_slots[i] == '9:00-9:30':
        rebecca_meeting += If(x[friends.index('Rebecca')*6 + locations.index('Chinatown')], 90, 0)
    else:
        rebecca_meeting += 0
s.add(rebecca_meeting >= 90)

# Meet Robert for at least 30 minutes
robert_meeting = 0
for i in range(num_time_slots):
    if time_slots[i] == '9:00-10:00' or time_slots[i] == '8:30-10:00':
        robert_meeting += If(x[friends.index('Robert')*6 + locations.index('The Castro')], 30, 0)
    else:
        robert_meeting += 0
s.add(robert_meeting >= 30)

# Ensure that you visit each location at most once
for i in range(num_time_slots):
    for j in range(len(friends)):
        s.add(AtMostOne([x[k*6 + locations.index(time_slots[i].split('-')[0])] for k in range(len(friends))]))

# Ensure that you don't visit a location before arriving
for i in range(num_time_slots):
    for j in range(num_time_slots):
        if time_slots[j].split('-')[0] < time_slots[i].split('-')[0]:
            s.add(Implies(x[friends.index('Andrew')*6 + locations.index(time_slots[i].split('-')[0])], Not(x[friends.index('Andrew')*6 + locations.index(time_slots[j].split('-')[0])])))

# Solve the problem
s.check()
model = s.model()

# Print the solution
print('SOLUTION:')
for friend in friends:
    for location in locations:
        if model.evaluate(x[friends.index(friend)*6 + locations.index(location)]).as_bool():
            print(f'Meet {friend} at {location} for {model.evaluate(If(x[friends.index(friend)*6 + locations.index(location)], 1, 0)) * 60} minutes')