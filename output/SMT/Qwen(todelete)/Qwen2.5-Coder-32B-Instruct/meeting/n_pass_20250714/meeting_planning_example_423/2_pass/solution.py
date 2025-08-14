from z3 import *

# Define the start time variables for each friend
jason_start = Int('jason_start')
melissa_start = Int('melissa_start')
brian_start = Int('brian_start')
elizabeth_start = Int('elizabeth_start')
laura_start = Int('laura_start')

# Define binary variables to indicate if we meet each person
meet_jason = Bool('meet_jason')
meet_melissa = Bool('meet_melissa')
meet_brian = Bool('meet_brian')
meet_elizabeth = Bool('meet_elizabeth')
meet_laura = Bool('meet_laura')

# Define the solver
solver = Solver()

# Add constraints for availability and minimum meeting duration
# Jason: 1:00PM to 8:45PM, 90 minutes
solver.add(Implies(meet_jason, jason_start >= 13 * 60))  # 1:00PM in minutes
solver.add(Implies(meet_jason, jason_start + 90 <= 8.75 * 60))  # 8:45PM in minutes

# Melissa: 6:45PM to 8:15PM, 45 minutes
solver.add(Implies(meet_melissa, melissa_start >= 18.75 * 60))  # 6:45PM in minutes
solver.add(Implies(meet_melissa, melissa_start + 45 <= 8.25 * 60))  # 8:15PM in minutes

# Brian: 9:45AM to 9:45PM, 15 minutes
solver.add(Implies(meet_brian, brian_start >= 9.75 * 60))  # 9:45AM in minutes
solver.add(Implies(meet_brian, brian_start + 15 <= 21.75 * 60))  # 9:45PM in minutes

# Elizabeth: 8:45AM to 9:30PM, 105 minutes
solver.add(Implies(meet_elizabeth, elizabeth_start >= 8.75 * 60))  # 8:45AM in minutes
solver.add(Implies(meet_elizabeth, elizabeth_start + 105 <= 21.5 * 60))  # 9:30PM in minutes

# Laura: 2:15PM to 7:30PM, 75 minutes
solver.add(Implies(meet_laura, laura_start >= 14.25 * 60))  # 2:15PM in minutes
solver.add(Implies(meet_laura, laura_start + 75 <= 19.5 * 60))  # 7:30PM in minutes

# Travel times from Presidio to each location (in minutes)
travel_times = {
    'jason': 7,
    'melissa': 18,
    'brian': 23,
    'elizabeth': 12,
    'laura': 22
}

# Ensure that the start time of each meeting is after the arrival time plus travel time if we meet them
arrival_time = 9 * 60  # 9:00AM in minutes
solver.add(Implies(meet_jason, jason_start >= arrival_time + travel_times['jason']))
solver.add(Implies(meet_melissa, melissa_start >= arrival_time + travel_times['melissa']))
solver.add(Implies(meet_brian, brian_start >= arrival_time + travel_times['brian']))
solver.add(Implies(meet_elizabeth, elizabeth_start >= arrival_time + travel_times['elizabeth']))
solver.add(Implies(meet_laura, laura_start >= arrival_time + travel_times['laura']))

# Ensure we meet exactly 5 people
solver.add(meet_jason + meet_melissa + meet_brian + meet_elizabeth + meet_laura == 5)

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    if model[meet_jason]:
        print(f"Meet Jason at: {model[jason_start].as_long() // 60}:{model[jason_start].as_long() % 60:02}")
    if model[meet_melissa]:
        print(f"Meet Melissa at: {model[melissa_start].as_long() // 60}:{model[melissa_start].as_long() % 60:02}")
    if model[meet_brian]:
        print(f"Meet Brian at: {model[brian_start].as_long() // 60}:{model[brian_start].as_long() % 60:02}")
    if model[meet_elizabeth]:
        print(f"Meet Elizabeth at: {model[elizabeth_start].as_long() // 60}:{model[elizabeth_start].as_long() % 60:02}")
    if model[meet_laura]:
        print(f"Meet Laura at: {model[laura_start].as_long() // 60}:{model[laura_start].as_long() % 60:02}")
else:
    print("No solution found.")