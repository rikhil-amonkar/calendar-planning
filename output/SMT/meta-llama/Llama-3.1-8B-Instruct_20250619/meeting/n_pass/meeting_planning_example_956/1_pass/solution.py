from z3 import *

# Define the variables
start_time = 0
end_time = 720  # 720 minutes in a day
friends = ['William', 'Joshua', 'Joseph', 'David', 'Brian', 'Karen', 'Anthony', 'Matthew', 'Helen', 'Jeffrey']
locations = ['The Castro', 'Alamo Square', 'Richmond District', 'Financial District', 'Union Square', 'Fisherman\'s Wharf', 'Marina District', 'Haight-Ashbury', 'Mission District', 'Pacific Heights', 'Golden Gate Park']

# Define the travel times
travel_times = {
    'The Castro': {'Alamo Square': 8, 'Richmond District': 16, 'Financial District': 21, 'Union Square': 19, 'Fisherman\'s Wharf': 24, 'Marina District': 21, 'Haight-Ashbury': 6, 'Mission District': 7, 'Pacific Heights': 16, 'Golden Gate Park': 11},
    'Alamo Square': {'The Castro': 8, 'Richmond District': 11, 'Financial District': 17, 'Union Square': 14, 'Fisherman\'s Wharf': 19, 'Marina District': 15, 'Haight-Ashbury': 5, 'Mission District': 10, 'Pacific Heights': 10, 'Golden Gate Park': 9},
    'Richmond District': {'The Castro': 16, 'Alamo Square': 13, 'Financial District': 22, 'Union Square': 21, 'Fisherman\'s Wharf': 18, 'Marina District': 9, 'Haight-Ashbury': 10, 'Mission District': 20, 'Pacific Heights': 10, 'Golden Gate Park': 9},
    'Financial District': {'The Castro': 20, 'Alamo Square': 17, 'Richmond District': 21, 'Union Square': 9, 'Fisherman\'s Wharf': 10, 'Marina District': 15, 'Haight-Ashbury': 19, 'Mission District': 17, 'Pacific Heights': 13, 'Golden Gate Park': 23},
    'Union Square': {'The Castro': 17, 'Alamo Square': 15, 'Richmond District': 20, 'Financial District': 9, 'Fisherman\'s Wharf': 15, 'Marina District': 18, 'Haight-Ashbury': 18, 'Mission District': 14, 'Pacific Heights': 15, 'Golden Gate Park': 22},
    'Fisherman\'s Wharf': {'The Castro': 27, 'Alamo Square': 21, 'Richmond District': 18, 'Financial District': 11, 'Union Square': 13, 'Marina District': 9, 'Haight-Ashbury': 22, 'Mission District': 22, 'Pacific Heights': 12, 'Golden Gate Park': 25},
    'Marina District': {'The Castro': 22, 'Alamo Square': 15, 'Richmond District': 11, 'Financial District': 17, 'Union Square': 16, 'Fisherman\'s Wharf': 10, 'Haight-Ashbury': 16, 'Mission District': 20, 'Pacific Heights': 7, 'Golden Gate Park': 18},
    'Haight-Ashbury': {'The Castro': 6, 'Alamo Square': 5, 'Richmond District': 10, 'Financial District': 21, 'Union Square': 19, 'Fisherman\'s Wharf': 23, 'Marina District': 17, 'Mission District': 11, 'Pacific Heights': 12, 'Golden Gate Park': 7},
    'Mission District': {'The Castro': 7, 'Alamo Square': 11, 'Richmond District': 20, 'Financial District': 15, 'Union Square': 15, 'Fisherman\'s Wharf': 22, 'Marina District': 19, 'Haight-Ashbury': 12, 'Pacific Heights': 16, 'Golden Gate Park': 17},
    'Pacific Heights': {'The Castro': 16, 'Alamo Square': 10, 'Richmond District': 12, 'Financial District': 13, 'Union Square': 12, 'Fisherman\'s Wharf': 13, 'Marina District': 6, 'Haight-Ashbury': 11, 'Mission District': 15, 'Golden Gate Park': 15},
    'Golden Gate Park': {'The Castro': 13, 'Alamo Square': 9, 'Richmond District': 7, 'Financial District': 26, 'Union Square': 22, 'Fisherman\'s Wharf': 24, 'Marina District': 16, 'Haight-Ashbury': 7, 'Mission District': 17, 'Pacific Heights': 16}
}

# Define the constraints
s = Solver()

# Define the variables
visit_times = {}
for friend in friends:
    visit_times[friend] = [Int(friend + 'VisitTime') for _ in range(len(locations))]

# Add constraints
for friend in friends:
    for i, location in enumerate(locations):
        s.add(visit_times[friend][i] >= start_time)
        s.add(visit_times[friend][i] <= end_time)

# William
s.add(visit_times['William'][0] >= 3 * 60)  # William arrives at 3:15PM
s.add(visit_times['William'][0] <= 5 * 60)  # William leaves at 5:15PM
s.add(visit_times['William'][0] + 60 >= visit_times['William'][0])  # Meet William for at least 60 minutes

# Joshua
s.add(visit_times['Joshua'][1] >= 0)  # Joshua arrives at 7:00AM
s.add(visit_times['Joshua'][1] <= 8 * 60)  # Joshua leaves at 8:00PM
s.add(visit_times['Joshua'][1] + 15 >= visit_times['Joshua'][1])  # Meet Joshua for at least 15 minutes

# Joseph
s.add(visit_times['Joseph'][2] >= 11 * 60)  # Joseph arrives at 11:15AM
s.add(visit_times['Joseph'][2] <= 13 * 60)  # Joseph leaves at 1:30PM
s.add(visit_times['Joseph'][2] + 15 >= visit_times['Joseph'][2])  # Meet Joseph for at least 15 minutes

# David
s.add(visit_times['David'][3] >= 4 * 60)  # David arrives at 4:45PM
s.add(visit_times['David'][3] <= 7 * 60)  # David leaves at 7:15PM
s.add(visit_times['David'][3] + 45 >= visit_times['David'][3])  # Meet David for at least 45 minutes

# Brian
s.add(visit_times['Brian'][4] >= 1 * 60)  # Brian arrives at 1:45PM
s.add(visit_times['Brian'][4] <= 8 * 60)  # Brian leaves at 8:45PM
s.add(visit_times['Brian'][4] + 105 >= visit_times['Brian'][4])  # Meet Brian for at least 105 minutes

# Karen
s.add(visit_times['Karen'][5] >= 11 * 60)  # Karen arrives at 11:30AM
s.add(visit_times['Karen'][5] <= 6 * 60)  # Karen leaves at 6:30PM
s.add(visit_times['Karen'][5] + 15 >= visit_times['Karen'][5])  # Meet Karen for at least 15 minutes

# Anthony
s.add(visit_times['Anthony'][6] >= 0)  # Anthony arrives at 7:15AM
s.add(visit_times['Anthony'][6] <= 1 * 60)  # Anthony leaves at 10:30AM
s.add(visit_times['Anthony'][6] + 30 >= visit_times['Anthony'][6])  # Meet Anthony for at least 30 minutes

# Matthew
s.add(visit_times['Matthew'][7] >= 5 * 60)  # Matthew arrives at 5:15PM
s.add(visit_times['Matthew'][7] <= 7 * 60)  # Matthew leaves at 7:15PM
s.add(visit_times['Matthew'][7] + 120 >= visit_times['Matthew'][7])  # Meet Matthew for at least 120 minutes

# Helen
s.add(visit_times['Helen'][8] >= 0)  # Helen arrives at 8:00AM
s.add(visit_times['Helen'][8] <= 12 * 60)  # Helen leaves at 12:00PM
s.add(visit_times['Helen'][8] + 75 >= visit_times['Helen'][8])  # Meet Helen for at least 75 minutes

# Jeffrey
s.add(visit_times['Jeffrey'][9] >= 7 * 60)  # Jeffrey arrives at 7:00PM
s.add(visit_times['Jeffrey'][9] <= 9 * 60)  # Jeffrey leaves at 9:30PM
s.add(visit_times['Jeffrey'][9] + 60 >= visit_times['Jeffrey'][9])  # Meet Jeffrey for at least 60 minutes

# Travel times
for friend in friends:
    for i, location in enumerate(locations):
        for j, location2 in enumerate(locations):
            if i!= j:
                s.add(visit_times[friend][i] + travel_times[location][location2] <= visit_times[friend][j])

# Solve
if s.check() == sat:
    model = s.model()
    print("SOLUTION:")
    for friend in friends:
        visit_times[friend] = [model[visit_times[friend][i]].as_long() for i in range(len(locations))]
        print(f"{friend} visits:")
        for i, location in enumerate(locations):
            print(f"  {location}: {visit_times[friend][i]} minutes")
else:
    print("No solution found")