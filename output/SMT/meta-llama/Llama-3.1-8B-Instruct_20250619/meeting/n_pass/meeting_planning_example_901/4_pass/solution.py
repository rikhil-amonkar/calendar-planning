from z3 import *

# Define the variables
locations = ['Russian Hill', 'Pacific Heights', 'North Beach', 'Golden Gate Park', 'Embarcadero', 
             'Haight-Ashbury', 'Fisherman\'s Wharf', 'Mission District', 'Alamo Square', 'Bayview', 
             'Richmond District']
friends = ['Emily', 'Helen', 'Kimberly', 'James', 'Linda', 'Paul', 'Anthony', 'Nancy', 'William', 'Margaret']
times = ['9:00AM', '10:30AM', '1:45PM', '6:45PM', '7:15PM', '7:30AM', '8:00AM', '8:30AM', '9:15AM', '2:45PM', '3:15PM', '5:30PM', '6:15PM', '6:45PM', '8:30PM']
travel_times = {
    'Russian Hill': {'Pacific Heights': 7, 'North Beach': 5, 'Golden Gate Park': 21, 'Embarcadero': 8, 
                     'Haight-Ashbury': 17, 'Fisherman\'s Wharf': 7, 'Mission District': 16, 
                     'Alamo Square': 15, 'Bayview': 23, 'Richmond District': 14},
    'Pacific Heights': {'Russian Hill': 7, 'North Beach': 9, 'Golden Gate Park': 15, 'Embarcadero': 10, 
                        'Haight-Ashbury': 11, 'Fisherman\'s Wharf': 13, 'Mission District': 15, 
                        'Alamo Square': 10, 'Bayview': 22, 'Richmond District': 12},
    'North Beach': {'Russian Hill': 4, 'Pacific Heights': 8, 'Golden Gate Park': 22, 'Embarcadero': 6, 
                    'Haight-Ashbury': 18, 'Fisherman\'s Wharf': 5, 'Mission District': 18, 
                    'Alamo Square': 16, 'Bayview': 25, 'Richmond District': 18},
    'Golden Gate Park': {'Russian Hill': 19, 'Pacific Heights': 16, 'North Beach': 23, 'Embarcadero': 25, 
                         'Haight-Ashbury': 7, 'Fisherman\'s Wharf': 24, 'Mission District': 17, 
                         'Alamo Square': 9, 'Bayview': 23, 'Richmond District': 7},
    'Embarcadero': {'Russian Hill': 8, 'Pacific Heights': 11, 'North Beach': 5, 'Golden Gate Park': 25, 
                    'Haight-Ashbury': 21, 'Fisherman\'s Wharf': 6, 'Mission District': 20, 
                    'Alamo Square': 19, 'Bayview': 21, 'Richmond District': 21},
    'Haight-Ashbury': {'Russian Hill': 17, 'Pacific Heights': 12, 'North Beach': 19, 'Embarcadero': 20, 
                       'Golden Gate Park': 7, 'Fisherman\'s Wharf': 23, 'Mission District': 11, 
                       'Alamo Square': 5, 'Bayview': 18, 'Richmond District': 10},
    'Fisherman\'s Wharf': {'Russian Hill': 7, 'Pacific Heights': 12, 'North Beach': 6, 'Embarcadero': 8, 
                          'Haight-Ashbury': 22, 'Golden Gate Park': 25, 'Mission District': 22, 
                          'Alamo Square': 21, 'Bayview': 26, 'Richmond District': 18},
    'Mission District': {'Russian Hill': 15, 'Pacific Heights': 16, 'North Beach': 17, 'Embarcadero': 19, 
                         'Haight-Ashbury': 12, 'Fisherman\'s Wharf': 22, 'Golden Gate Park': 17, 
                         'Alamo Square': 11, 'Bayview': 14, 'Richmond District': 20},
    'Alamo Square': {'Russian Hill': 13, 'Pacific Heights': 10, 'North Beach': 15, 'Embarcadero': 16, 
                     'Haight-Ashbury': 5, 'Fisherman\'s Wharf': 19, 'Mission District': 10, 
                     'Bayview': 16, 'Richmond District': 11},
    'Bayview': {'Russian Hill': 23, 'Pacific Heights': 23, 'North Beach': 22, 'Embarcadero': 19, 
                'Haight-Ashbury': 19, 'Fisherman\'s Wharf': 25, 'Mission District': 13, 
                'Alamo Square': 16, 'Richmond District': 25},
    'Richmond District': {'Russian Hill': 13, 'Pacific Heights': 10, 'North Beach': 17, 'Embarcadero': 19, 
                          'Haight-Ashbury': 10, 'Fisherman\'s Wharf': 18, 'Mission District': 20, 
                          'Alamo Square': 13, 'Bayview': 27}
}

# Define the constraints
s = Solver()

# Define the variables
x = [Bool(friend) for friend in friends]
y = [Int(friend +'time') for friend in friends]
z = [Int(friend +'location') for friend in friends]

# Constraints for each friend
for i, friend in enumerate(friends):
    if friend == 'Emily':
        s.add(x[i])
        s.add(y[i] >= 90)
        s.add(y[i] <= 135)
        s.add(z[i] == 1)  # Pacific Heights
    elif friend == 'Helen':
        s.add(x[i])
        s.add(y[i] >= 30)
        s.add(y[i] <= 45)
        s.add(z[i] == 2)  # North Beach
    elif friend == 'Kimberly':
        s.add(x[i])
        s.add(y[i] >= 75)
        s.add(y[i] <= 150)
        s.add(z[i] == 3)  # Golden Gate Park
    elif friend == 'James':
        s.add(x[i])
        s.add(y[i] >= 30)
        s.add(y[i] <= 45)
        s.add(z[i] == 4)  # Embarcadero
    elif friend == 'Linda':
        s.add(x[i])
        s.add(y[i] >= 15)
        s.add(y[i] <= 30)
        s.add(z[i] == 5)  # Haight-Ashbury
    elif friend == 'Paul':
        s.add(x[i])
        s.add(y[i] >= 90)
        s.add(y[i] <= 180)
        s.add(z[i] == 6)  # Fisherman's Wharf
    elif friend == 'Anthony':
        s.add(x[i])
        s.add(y[i] >= 105)
        s.add(y[i] <= 210)
        s.add(z[i] == 7)  # Mission District
    elif friend == 'Nancy':
        s.add(x[i])
        s.add(y[i] >= 120)
        s.add(y[i] <= 240)
        s.add(z[i] == 8)  # Alamo Square
    elif friend == 'William':
        s.add(x[i])
        s.add(y[i] >= 120)
        s.add(y[i] <= 240)
        s.add(z[i] == 9)  # Bayview
    elif friend == 'Margaret':
        s.add(x[i])
        s.add(y[i] >= 45)
        s.add(y[i] <= 90)
        s.add(z[i] == 10)  # Richmond District

# Add constraints for travel times
for i, friend in enumerate(friends):
    if i == 0:  # Emily
        s.add(y[0] >= 15 + 7)
    elif i == 1:  # Helen
        s.add(And(y[1] >= 135 + 9, y[1] <= 180))
    elif i == 2:  # Kimberly
        s.add(And(y[2] >= 180 + 22, y[2] <= 255))
    elif i == 3:  # James
        s.add(And(y[3] >= 45 + 8, y[3] <= 60))
    elif i == 4:  # Linda
        s.add(And(y[4] >= 0 + 17, y[4] <= 30))
    elif i == 5:  # Paul
        s.add(And(y[5] >= 180 + 6, y[5] <= 270))
    elif i == 6:  # Anthony
        s.add(And(y[6] >= 0 + 16, y[6] <= 210))
    elif i == 7:  # Nancy
        s.add(And(y[7] >= 15 + 15, y[7] <= 240))
    elif i == 8:  # William
        s.add(And(y[8] >= 180 + 22, y[8] <= 270))
    elif i == 9:  # Margaret
        s.add(And(y[9] >= 75 + 10, y[9] <= 180))

# Add constraint to meet exactly 7 people
s.add(And(x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7], x[8], x[9]))

# Add constraint to ensure that the times are correct
s.add(And(y[0] >= 90, y[1] >= 135 + 9, y[2] >= 180 + 22, y[3] >= 45 + 8, y[4] >= 0 + 17, 
         y[5] >= 180 + 6, y[6] >= 0 + 16, y[7] >= 15 + 15, y[8] >= 180 + 22, y[9] >= 75 + 10))

# Check if the solution is sat
if s.check() == sat:
    model = s.model()
    print('SOLUTION:')
    for friend, time, location in zip(friends, [model[y[i]].as_long() for i in range(10)], 
                                     [model[z[i]].as_long() for i in range(10)]):
        print(f'{friend}: {time} minutes, {location}')
else:
    print('NO SOLUTION')