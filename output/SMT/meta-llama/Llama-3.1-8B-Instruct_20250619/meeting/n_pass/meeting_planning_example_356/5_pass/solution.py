from z3 import *

# Define the travel distances in minutes
distances = {
    'Bayview': {'North Beach': 21, 'Presidio': 31, 'Haight-Ashbury': 19, 'Union Square': 17},
    'North Beach': {'Bayview': 22, 'Presidio': 17, 'Haight-Ashbury': 18, 'Union Square': 7},
    'Presidio': {'Bayview': 31, 'North Beach': 18, 'Haight-Ashbury': 15, 'Union Square': 22},
    'Haight-Ashbury': {'Bayview': 18, 'North Beach': 19, 'Presidio': 15, 'Union Square': 17},
    'Union Square': {'Bayview': 15, 'North Beach': 10, 'Presidio': 24, 'Haight-Ashbury': 18}
}

# Define the constraints
start_time = 0
barbara_start = 1 * 60 + 45  # 1:45 PM
barbara_end = 8 * 60 + 15  # 8:15 PM
margaret_start = 10 * 60 + 15  # 10:15 AM
margaret_end = 3 * 60 + 15  # 3:15 PM
kevin_start = 20 * 60 + 0  # 8:00 PM
kevin_end = 20 * 60 + 45  # 8:45 PM
kimberly_start = 7 * 60 + 45  # 7:45 AM
kimberly_end = 4 * 60 + 45  # 4:45 PM

# Define the variables
s = Solver()

# Variables to represent the times spent at each location
bayview_time = Int('bayview_time')
north_beach_time = Int('north_beach_time')
presidio_time = Int('presidio_time')
haight_ashbury_time = Int('haight_ashbury_time')
union_square_time = Int('union_square_time')

# Variables to represent the locations visited
visited_locations = [Bool('visited_bayview'), Bool('visited_north_beach'), Bool('visited_presidio'), Bool('visited_haight_ashbury'), Bool('visited_union_square')]

# Variables to represent the people met
people_met = [Bool('met_barbara'), Bool('met_margaret'), Bool('met_kevin'), Bool('met_kimberly')]

# Constraints
s.add(bayview_time >= 0)
s.add(north_beach_time >= 0)
s.add(presidio_time >= 0)
s.add(haight_ashbury_time >= 0)
s.add(union_square_time >= 0)

# Barbara
s.add(north_beach_time >= 60)  # Minimum 60 minutes with Barbara
s.add(And(bayview_time + distances['Bayview']['North Beach'] <= barbara_start,
          north_beach_time + distances['North Beach']['Bayview'] >= barbara_start,
          north_beach_time + distances['North Beach']['Bayview'] <= barbara_end))

# Margaret
s.add(presidio_time >= 30)  # Minimum 30 minutes with Margaret
s.add(And(bayview_time + distances['Bayview']['Presidio'] <= margaret_start,
          presidio_time + distances['Presidio']['Bayview'] >= margaret_start,
          presidio_time + distances['Presidio']['Bayview'] <= margaret_end))

# Kevin
s.add(haight_ashbury_time >= 30)  # Minimum 30 minutes with Kevin
s.add(And(bayview_time + distances['Bayview']['Haight-Ashbury'] <= kevin_start,
          haight_ashbury_time + distances['Haight-Ashbury']['Bayview'] >= kevin_start,
          haight_ashbury_time + distances['Haight-Ashbury']['Bayview'] <= kevin_end))

# Kimberly
s.add(union_square_time >= 30)  # Minimum 30 minutes with Kimberly
s.add(And(bayview_time + distances['Bayview']['Union Square'] <= kimberly_end,
          union_square_time + distances['Union Square']['Bayview'] >= kimberly_start,
          union_square_time + distances['Union Square']['Bayview'] <= kimberly_end))

# Total time constraint
total_time = bayview_time + north_beach_time + presidio_time + haight_ashbury_time + union_square_time
s.add(total_time <= 24 * 60)  # Maximum 24 hours

# Exactly 4 people met constraint
s.add(Or(people_met))
s.add(And(Not(people_met[0]) + bayview_time == 0,
          Not(people_met[1]) + north_beach_time == 0,
          Not(people_met[2]) + presidio_time == 0,
          Not(people_met[3]) + haight_ashbury_time == 0))

# At least one location visited constraint
s.add(Or(visited_locations))
s.add(And(Not(visited_locations[0]) + (bayview_time == 0),
          Not(visited_locations[1]) + (north_beach_time == 0),
          Not(visited_locations[2]) + (presidio_time == 0),
          Not(visited_locations[3]) + (haight_ashbury_time == 0)))

# Check if the solution is feasible
if s.check() == sat:
    model = s.model()
    bayview_time_val = model[bayview_time].as_long()
    north_beach_time_val = model[north_beach_time].as_long()
    presidio_time_val = model[presidio_time].as_long()
    haight_ashbury_time_val = model[haight_ashbury_time].as_long()
    union_square_time_val = model[union_square_time].as_long()
    visited_locations_val = [model[loc].as_bool() for loc in visited_locations]
    people_met_val = [model[people_met[i]].as_bool() for i in range(4)]
    print("Optimal schedule:")
    print(f"Bayview: {bayview_time_val} minutes")
    print(f"North Beach: {north_beach_time_val} minutes")
    print(f"Presidio: {presidio_time_val} minutes")
    print(f"Haight-Ashbury: {haight_ashbury_time_val} minutes")
    print(f"Union Square: {union_square_time_val} minutes")
    print(f"Visited locations: {visited_locations_val}")
    print(f"People met: {people_met_val}")
else:
    print("No feasible solution exists")