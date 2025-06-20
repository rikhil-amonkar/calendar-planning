from z3 import *

# Define the travel distances
distances = {
    'Nob Hill': {'Presidio': 17, 'North Beach': 8, 'Fisherman\'s Wharf': 11, 'Pacific Heights': 8},
    'Presidio': {'Nob Hill': 18, 'North Beach': 18, 'Fisherman\'s Wharf': 19, 'Pacific Heights': 11},
    'North Beach': {'Nob Hill': 7, 'Presidio': 17, 'Fisherman\'s Wharf': 5, 'Pacific Heights': 8},
    'Fisherman\'s Wharf': {'Nob Hill': 11, 'Presidio': 17, 'North Beach': 6, 'Pacific Heights': 12},
    'Pacific Heights': {'Nob Hill': 8, 'Presidio': 11, 'North Beach': 9, 'Fisherman\'s Wharf': 13}
}

# Define the constraints
s = Solver()
friends = ['Jeffrey', 'Steven', 'Barbara', 'John']
times = ['9:00AM', '8:00AM-10:00AM', '1:30PM-10:00PM', '6:00PM-9:30PM', '9:00AM-1:30PM']

# Define the variables
x = {}
for friend in friends:
    x[friend] = [Bool(f'{friend}_{i}') for i in range(len(times))]

# Define the constraints
for friend in friends:
    if friend == 'Jeffrey':
        s.add(Or([x[friend][0], x[friend][1]]))
        s.add(If(x[friend][0], x[friend][1], False))
        s.add(If(x[friend][1], x[friend][0], False))
        s.add(Implies(x[friend][0], x[friend][0] * 105))
        s.add(Implies(x[friend][1], x[friend][1] * 105))
    elif friend == 'Steven':
        s.add(x[friend][2])
        s.add(Implies(x[friend][2], x[friend][2] * 45))
    elif friend == 'Barbara':
        s.add(Implies(x[friend][3], x[friend][3] * 30))
    elif friend == 'John':
        s.add(x[friend][0])
        s.add(Implies(x[friend][0], x[friend][0] * 15))

# Add constraints for travel times
for i in range(len(friends)):
    for j in range(len(friends)):
        if i!= j:
            for time in range(len(times)):
                if times[i] == times[j]:
                    s.add(Not(And(x[friends[i]][time], x[friends[j]][time])))

# Add constraints for meeting times
for friend in friends:
    for time in range(len(times)):
        if times[0] == times[time]:
            s.add(Not(And(x[friend][time], x[friend][time] * 60)))

# Solve the problem
s.add(Or([x[friend][time] for friend in friends for time in range(len(times))]))
s.check()
m = s.model()

# Print the solution
print('SOLUTION:')
for friend in friends:
    for time in range(len(times)):
        if m[x[friend][time]]:
            print(f'Meet {friend} at {times[time]} for {distances["Nob Hill"][friend] if times[time] == "9:00AM" else (distances[times[time].split('-')[0].split(" ")[0]]["Nob Hill"] if times[time].split('-')[0].split(" ")[1] == "AM" else distances[times[time].split('-')[0].split(" ")[0]]["Nob Hill"])} minutes')