from z3 import *

# Define the variables
s = Solver()

# Define the time slots for each person
mary_start = 9 * 60  # 9:00 AM
mary_end = mary_start + 3 * 60  # 11:45 AM
kevin_start = 10 * 60  # 10:15 AM
kevin_end = kevin_start + 6 * 60  # 4:15 PM
deborah_start = 3 * 60  # 3:00 PM
deborah_end = deborah_start + 4 * 60  # 7:15 PM
stephanie_start = 10 * 60  # 10:00 AM
stephanie_end = stephanie_start + 7 * 60  # 5:15 PM
emily_start = 11 * 60  # 11:30 AM
emily_end = emily_start + 10 * 60  # 9:45 PM

# Define the meeting requirements
mary_meet_min = 45 * 60  # 45 minutes
kevin_meet_min = 90 * 60  # 90 minutes
deborah_meet_min = 120 * 60  # 120 minutes
stephanie_meet_min = 120 * 60  # 120 minutes
emily_meet_min = 105 * 60  # 105 minutes

# Define the locations and their distances
locations = {
    'Embarcadero': 0,
    'Golden Gate Park': 25,
    'Haight-Ashbury': 21,
    'Bayview': 21,
    'Presidio': 20,
    'Financial District': 5
}

# Define the variables for the schedule
x = [Bool(f'meet_{i}') for i in range(5)]  # meet Mary, Kevin, Deborah, Stephanie, Emily
y = [Int(f'time_{i}') for i in range(5)]  # time spent with each person

# Add constraints for the schedule
s.add(x[0])  # must meet Mary
s.add(y[0] >= mary_meet_min)
s.add(y[0] <= mary_end - mary_start)

s.add(Or(x[1], x[2], x[3], x[4]))  # can meet Kevin, Deborah, Stephanie, or Emily
s.add(Implies(x[1], And(y[1] >= kevin_meet_min, y[1] <= kevin_end - kevin_start)))
s.add(Implies(x[2], And(y[2] >= kevin_meet_min, y[2] <= kevin_end - kevin_start)))
s.add(Implies(x[3], And(y[3] >= deborah_meet_min, y[3] <= deborah_end - deborah_start)))
s.add(Implies(x[4], And(y[4] >= stephanie_meet_min, y[4] <= stephanie_end - stephanie_start)))

# Add constraints for the travel times
s.add(y[0] >= locations['Embarcadero'] + locations['Golden Gate Park'])
s.add(y[1] >= locations['Golden Gate Park'] + locations['Haight-Ashbury'])
s.add(y[2] >= locations['Haight-Ashbury'] + locations['Bayview'])
s.add(y[3] >= locations['Bayview'] + locations['Presidio'])
s.add(y[4] >= locations['Presidio'] + locations['Financial District'])

# Solve the problem
if s.check() == sat:
    model = s.model()
    print("SOLUTION:")
    for i in range(5):
        print(f"Meet {['Mary', 'Kevin', 'Deborah', 'Stephanie', 'Emily'][i]} for {model[y[i]].as_long()} minutes")
else:
    print("No solution found")