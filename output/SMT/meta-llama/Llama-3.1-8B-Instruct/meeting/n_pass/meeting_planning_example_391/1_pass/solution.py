from z3 import *

# Define the variables
start_time = 0
end_time = 1430  # 2:30 PM
friends = ['Kevin', 'Kimberly', 'Joseph', 'Thomas']
locations = ['Sunset District', 'Alamo Square', 'Russian Hill', 'Presidio', 'Financial District']
travel_times = {
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Financial District'): 30,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Presidio'): 18,
    ('Alamo Square', 'Financial District'): 17,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Financial District'): 11,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Alamo Square'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Financial District'): 23,
    ('Financial District', 'Sunset District'): 31,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Russian Hill'): 10,
    ('Financial District', 'Presidio'): 22
}

s = Optimize()

# Define the decision variables
x = [[Bool(f'x_{friend}_{location}') for location in locations] for friend in friends]
y = [[Bool(f'y_{friend}_{location}_{next_location}') for next_location in locations for location in locations] for friend in friends]
z = [Int(f'z_{friend}') for friend in friends]

# Add constraints
for friend in friends:
    s.add(z[friend] >= 0)
    s.add(z[friend] <= 1430 - start_time)

for friend in friends:
    for location in locations:
        s.add(x[friend][location] == 0)
        for next_location in locations:
            s.add(y[friend][location][next_location] == 0)

for friend in friends:
    for location in locations:
        s.add(If(x[friend][location], z[friend] - travel_times[(location, 'Sunset District')] >= 0, True))

for friend in friends:
    for location in locations:
        for next_location in locations:
            if location!= next_location:
                s.add(If(y[friend][location][next_location], z[friend] - travel_times[(location, next_location)] >= 0, True))

for friend in friends:
    s.add(z[friend] >= 75 * x[friend]['Alamo Square'])
    s.add(z[friend] >= 30 * x[friend]['Russian Hill'])
    s.add(z[friend] >= 45 * x[friend]['Presidio'])
    s.add(z[friend] >= 45 * x[friend]['Financial District'])

# Add objective function
s.minimize(z[0] + z[1] + z[2] + z[3])

# Solve the problem
result = s.check()
if result == sat:
    model = s.model()
    print("SOLUTION:")
    for friend in friends:
        print(f"Friend: {friend}")
        for location in locations:
            if model[x[friend][location]].as_bool():
                print(f"  Visit {location}: Yes")
            else:
                print(f"  Visit {location}: No")
        for location in locations:
            for next_location in locations:
                if location!= next_location:
                    if model[y[friend][location][next_location]].as_bool():
                        print(f"  Travel from {location} to {next_location}: Yes")
                    else:
                        print(f"  Travel from {location} to {next_location}: No")
        print(f"  Total time: {model[z[friend]]}")
        print()
else:
    print("No solution found")