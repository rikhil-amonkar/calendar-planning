from z3 import *

# Define the time points in minutes from 9:00 AM
start_time = 0  # 9:00 AM
sarah_start = 300  # 4:00 PM
sarah_end = 375  # 6:15 PM
jeffrey_start = 180  # 3:00 PM
jeffrey_end = 600  # 10:00 PM
brian_start = 300  # 4:00 PM
brian_end = 330  # 5:30 PM

# Define the travel times in minutes
travel_times = {
    ('Sunset District', 'North Beach'): 29,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Alamo Square'): 17,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Alamo Square'): 16,
    ('Union Square', 'Sunset District'): 26,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Alamo Square'): 15,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Union Square'): 14
}

# Define the locations
locations = ['Sunset District', 'North Beach', 'Union Square', 'Alamo Square']

# Create a solver instance
solver = Solver()

# Define variables for the start time at each location
start_times = {loc: Int(f'start_{loc}') for loc in locations}

# Add constraints for the start times
for loc in locations:
    solver.add(start_times[loc] >= start_time)

# Add constraints for the travel times
for (loc1, loc2), time in travel_times.items():
    solver.add(start_times[loc2] >= start_times[loc1] + time)

# Define variables for the end times at each location
end_times = {loc: Int(f'end_{loc}') for loc in locations}

# Add constraints for the end times
for loc in locations:
    solver.add(end_times[loc] >= start_times[loc])

# Define binary variables to indicate if a meeting with each friend occurs
meet_sarah = Bool('meet_sarah')
meet_jeffrey = Bool('meet_jeffrey')
meet_brian = Bool('meet_brian')

# Define constraints for meeting Sarah
sarah_meeting_start = Int('sarah_meeting_start')
sarah_meeting_end = Int('sarah_meeting_end')
solver.add(sarah_meeting_start >= sarah_start)
solver.add(sarah_meeting_start <= sarah_end - 60)  # Minimum 60 minutes meeting
solver.add(sarah_meeting_end == sarah_meeting_start + 60)
solver.add(sarah_meeting_end <= sarah_end)
solver.add(meet_sarah == And(sarah_meeting_start >= start_times['North Beach'], sarah_meeting_end <= end_times['North Beach']))

# Define constraints for meeting Jeffrey
jeffrey_meeting_start = Int('jeffrey_meeting_start')
jeffrey_meeting_end = Int('jeffrey_meeting_end')
solver.add(jeffrey_meeting_start >= jeffrey_start)
solver.add(jeffrey_meeting_start <= jeffrey_end - 75)  # Minimum 75 minutes meeting
solver.add(jeffrey_meeting_end == jeffrey_meeting_start + 75)
solver.add(jeffrey_meeting_end <= jeffrey_end)
solver.add(meet_jeffrey == And(jeffrey_meeting_start >= start_times['Union Square'], jeffrey_meeting_end <= end_times['Union Square']))

# Define constraints for meeting Brian
brian_meeting_start = Int('brian_meeting_start')
brian_meeting_end = Int('brian_meeting_end')
solver.add(brian_meeting_start >= brian_start)
solver.add(brian_meeting_start <= brian_end - 75)  # Minimum 75 minutes meeting
solver.add(brian_meeting_end == brian_meeting_start + 75)
solver.add(brian_meeting_end <= brian_end)
solver.add(meet_brian == And(brian_meeting_start >= start_times['Alamo Square'], brian_meeting_end <= end_times['Alamo Square']))

# Ensure exactly two meetings occur
solver.add(meet_sarah + meet_jeffrey + meet_brian == 2)

# Check if the solution is feasible
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    print(f"Meet Sarah: {model[meet_sarah]}")
    if model[meet_sarah]:
        print(f"Meeting Sarah from {model[sarah_meeting_start]} to {model[sarah_meeting_end]} minutes after 9:00 AM")
    print(f"Meet Jeffrey: {model[meet_jeffrey]}")
    if model[meet_jeffrey]:
        print(f"Meeting Jeffrey from {model[jeffrey_meeting_start]} to {model[jeffrey_meeting_end]} minutes after 9:00 AM")
    print(f"Meet Brian: {model[meet_brian]}")
    if model[meet_brian]:
        print(f"Meeting Brian from {model[brian_meeting_start]} to {model[brian_meeting_end]} minutes after 9:00 AM")
    for loc in locations:
        print(f"Start time at {loc}: {model[start_times[loc]]} minutes after 9:00 AM")
        print(f"End time at {loc}: {model[end_times[loc]]} minutes after 9:00 AM")
else:
    print("No solution found")