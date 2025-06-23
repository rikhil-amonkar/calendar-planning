from z3 import *

# Define the variables
start_time = 0
end_time = 12 * 60  # 12 hours in minutes
friends = ['helen', 'betty', 'amanda', 'kevin']
times = [9 * 60, 7 * 60, 7 * 60 + 45 * 60, 10 * 60 + 45 * 60]
locations = ['pacific_heights', 'north_beach', 'financial_district', 'alamo_square','mission_district']
distances = {
    'pacific_heights': {'north_beach': 8, 'financial_district': 13, 'alamo_square': 10,'mission_district': 15},
    'north_beach': {'pacific_heights': 9, 'financial_district': 8, 'alamo_square': 16,'mission_district': 18},
    'financial_district': {'pacific_heights': 13, 'north_beach': 7, 'alamo_square': 17,'mission_district': 17},
    'alamo_square': {'pacific_heights': 10, 'north_beach': 15, 'financial_district': 17,'mission_district': 10},
'mission_district': {'pacific_heights': 15, 'north_beach': 17, 'financial_district': 17, 'alamo_square': 11}
}

# Create a Z3 solver
s = Solver()

# Define the meeting times
meeting_times = {}
for friend in friends:
    if friend == 'helen':
        start_time_helen = 9 * 60
        end_time_helen = 5 * 60
        meeting_times[friend] = [start_time_helen, end_time_helen, 15]  # [start, end, min_time]
    elif friend == 'betty':
        start_time_betty = 7 * 60
        end_time_betty = 9 * 60
        meeting_times[friend] = [start_time_betty, end_time_betty, 90]
    elif friend == 'amanda':
        start_time_amanda = 7 * 60 + 45 * 60
        end_time_amanda = 9 * 60
        meeting_times[friend] = [start_time_amanda, end_time_amanda, 60]
    elif friend == 'kevin':
        start_time_kevin = 10 * 60 + 45 * 60
        end_time_kevin = 2 * 60 + 45 * 60
        meeting_times[friend] = [start_time_kevin, end_time_kevin, 45]

# Define the variables for the solver
x = [Int('x_' + str(i)) for i in range(len(friends) * 2)]
y = [Int('y_' + str(i)) for i in range(len(friends))]
z = [Int('z_' + str(i)) for i in range(len(friends))]
c = [Bool('c_' + str(i)) for i in range(len(friends))]
m = [Bool('m_' + str(i)) for i in range(len(friends))]
a = [Bool('a_' + str(i)) for i in range(len(friends) * len(friends))]
b = [Bool('b_' + str(i)) for i in range(len(friends) * len(friends))]
p = [Bool('p_' + str(i)) for i in range(len(friends) * len(friends))]

# Define the constraints
for i in range(len(friends)):
    s.add(x[2 * i] >= meeting_times[friends[i]][0])
    s.add(x[2 * i] <= meeting_times[friends[i]][1])
    s.add(x[2 * i + 1] >= meeting_times[friends[i]][2])
    s.add(x[2 * i + 1] <= meeting_times[friends[i]][1])
    s.add(y[i] >= x[2 * i])
    s.add(y[i] <= x[2 * i + 1])
    s.add(z[i] >= x[2 * i])
    s.add(z[i] <= x[2 * i + 1])
    s.add(c[i] == x[2 * i] <= 10 * 60)  # Only consider meetings before 10:00 AM

# Define the constraints for the locations
for i in range(len(friends)):
    for j in range(len(friends)):
        if j > i:
            s.add(y[i] + distances[locations[i]][locations[j]] >= x[2 * j])

# Define the constraint for the number of meetings
s.add(Or([m[0], m[1], m[2]]))  # Meet with at least one person
s.add(Not(Or([m[0], m[1], m[2], m[0] & m[1] & m[2]])))  # Meet with exactly three people

# Define the constraints for the meeting pairs
for i in range(len(friends)):
    for j in range(i + 1, len(friends)):
        s.add(a[i * len(friends) + j] == Or([x[2 * i] <= 10 * 60, x[2 * j] <= 10 * 60]))
        s.add(a[i * len(friends) + j] == Or([x[2 * i] <= 10 * 60, x[2 * j] >= 10 * 60]))
        s.add(a[i * len(friends) + j] == Or([x[2 * i] >= 10 * 60, x[2 * j] <= 10 * 60]))
        s.add(a[i * len(friends) + j] == Or([x[2 * i] >= 10 * 60, x[2 * j] >= 10 * 60]))

# Define the constraints for the meeting pairs
for i in range(len(friends)):
    for j in range(i + 1, len(friends)):
        s.add(b[i * len(friends) + j] == Or([x[2 * i] <= 10 * 60, x[2 * j] <= 10 * 60]))
        s.add(b[i * len(friends) + j] == Or([x[2 * i] <= 10 * 60, x[2 * j] >= 10 * 60]))
        s.add(b[i * len(friends) + j] == Or([x[2 * i] >= 10 * 60, x[2 * j] <= 10 * 60]))
        s.add(b[i * len(friends) + j] == Or([x[2 * i] >= 10 * 60, x[2 * j] >= 10 * 60]))

# Define the constraint for the meeting pairs
s.add(p[0 * len(friends) + 1] == a[0 * len(friends) + 1])
s.add(p[0 * len(friends) + 2] == a[0 * len(friends) + 2])
s.add(p[1 * len(friends) + 2] == a[1 * len(friends) + 2])

# Define the constraint for the meeting pairs
s.add(p[0 * len(friends) + 1] == b[0 * len(friends) + 1])
s.add(p[0 * len(friends) + 2] == b[0 * len(friends) + 2])
s.add(p[1 * len(friends) + 2] == b[1 * len(friends) + 2])

# Define the constraint for the meeting pairs
s.add(p[0 * len(friends) + 1] == p[0 * len(friends) + 2])
s.add(p[0 * len(friends) + 1] == p[1 * len(friends) + 2])

# Solve the problem
if s.check() == sat:
    model = s.model()
    print("SOLUTION:")
    count = 0
    for i in range(len(friends)):
        if model[m[i]]:
            count += 1
            print(f"Meet {friends[i]} at {model[x[2 * i]].as_long()} minutes past 9:00 AM for {model[z[i]].as_long()} minutes")
else:
    print("No solution found")