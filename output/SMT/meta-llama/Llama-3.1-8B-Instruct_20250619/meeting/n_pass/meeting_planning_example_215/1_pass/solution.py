from z3 import *

# Define the travel times
travel_times = {
    'Bayview to Embarcadero': 19,
    'Bayview to Richmond District': 25,
    'Bayview to Fisherman\'s Wharf': 25,
    'Embarcadero to Bayview': 21,
    'Embarcadero to Richmond District': 21,
    'Embarcadero to Fisherman\'s Wharf': 6,
    'Richmond District to Bayview': 26,
    'Richmond District to Embarcadero': 19,
    'Richmond District to Fisherman\'s Wharf': 18,
    'Fisherman\'s Wharf to Bayview': 26,
    'Fisherman\'s Wharf to Embarcadero': 8,
    'Fisherman\'s Wharf to Richmond District': 18
}

# Define the constraints
s = Optimize()

# Define the variables
x = [Bool(f'visit_{location}') for location in ['Embarcadero', 'Richmond District', 'Fisherman\'s Wharf']]
t = Int('time')
jason_time = Int('jason_time')
sandra_time = Int('sandra_time')

# Add constraints
s.add(And([x[0], t >= 9*60 + 45*60, t <= 7*60]))
s.add(And([x[1], t >= 9*60 + 6.5*60, t <= 9.75*60]))
s.add(And([x[2], t >= 9*60 + 4*60, t <= 4.75*60]))
s.add(t >= 9*60)
s.add(t <= 9.75*60)

# Add objective
s.add(If(x[0], jason_time, 0) + If(x[1], 120, 0) + If(x[2], 30, 0) >= 0)
s.add(jason_time >= 30)
s.add(sandra_time >= 120)

# Solve
result = s.check()

# Print the result
if result == sat:
    model = s.model()
    print('Best schedule:')
    for location in ['Embarcadero', 'Richmond District', 'Fisherman\'s Wharf']:
        if model.evaluate(x[travel_times.keys().index(f'Bayview to {location}')]).as_bool():
            print(f'Visit {location}')
    print(f'Time: {model.evaluate(t).as_long()} minutes')
    print(f'Meet Jessica for {model.evaluate(jason_time).as_long()} minutes')
    print(f'Meet Sandra for {model.evaluate(sandra_time).as_long()} minutes')
else:
    print('No solution found')