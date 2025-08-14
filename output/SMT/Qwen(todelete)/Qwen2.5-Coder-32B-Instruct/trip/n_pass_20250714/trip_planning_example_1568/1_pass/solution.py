from z3 import *
import json

# Define the solver
solver = Solver()

# Define the variables for the start day of each city
prague_start = Int('prague_start')
brussels_start = Int('brussels_start')
riga_start = Int('riga_start')
munich_start = Int('munich_start')
seville_start = Int('seville_start')
stockholm_start = Int('stockholm_start')
istanbul_start = Int('istanbul_start')
amsterdam_start = Int('amsterdam_start')
vienna_start = Int('vienna_start')
split_start = Int('split_start')

# Define the duration of stay in each city
prague_duration = 5
brussels_duration = 2
riga_duration = 2
munich_duration = 2
seville_duration = 3
stockholm_duration = 2
istanbul_duration = 2
amsterdam_duration = 3
vienna_duration = 5
split_duration = 3

# Define the constraints
# Total duration constraint
solver.add(prague_start + prague_duration <= 21)
solver.add(brussels_start + brussels_duration <= 21)
solver.add(riga_start + riga_duration <= 21)
solver.add(munich_start + munich_duration <= 21)
solver.add(seville_start + seville_duration <= 21)
solver.add(stockholm_start + stockholm_duration <= 21)
solver.add(istanbul_start + istanbul_duration <= 21)
solver.add(amsterdam_start + amsterdam_duration <= 21)
solver.add(vienna_start + vienna_duration <= 21)
solver.add(split_start + split_duration <= 21)

# Specific day constraints
solver.add(prague_start <= 1)  # To meet friend in Vienna between day 1 and day 5
solver.add(prague_start + prague_duration - 1 >= 4)  # To meet friend in Vienna between day 1 and day 5
solver.add(prague_start + 3 == 4)  # Annual show in Prague from day 5 to day 9
solver.add(prague_start + prague_duration - 1 == 8)  # Annual show in Prague from day 5 to day 9
solver.add(riga_start + 1 == 15)  # Meet friends in Riga between day 15 and day 16
solver.add(riga_start + riga_duration - 1 == 16)  # Meet friends in Riga between day 15 and day 16
solver.add(stockholm_start + 1 == 16)  # Conference in Stockholm on day 16 and day 17
solver.add(stockholm_start + stockholm_duration - 1 == 17)  # Conference in Stockholm on day 16 and day 17
solver.add(split_start + 1 == 11)  # Visit relatives in Split between day 11 and day 13
solver.add(split_start + split_duration - 1 == 13)  # Visit relatives in Split between day 11 and day 13

# Flight constraints (ensure that the cities can be reached by direct flights)
# We will use a helper function to add these constraints
def add_flight_constraints(solver, start1, duration1, start2, duration2, possible_flights):
    for i in range(duration1):
        for j in range(duration2):
            solver.add(Or(start1 + i != start2 + j, Or((start1 + i + 1 == start2 + j), (start2 + j + 1 == start1 + i), 
                                                        (start1 + i == start2 + j), 
                                                        Not(And(start1 + i < start2 + j, start1 + i + 1 > start2 + j)),
                                                        Not(And(start2 + j < start1 + i, start2 + j + 1 > start1 + i)))))

# List of possible direct flights as tuples (city1, city2)
possible_flights = [
    ('Riga', 'Stockholm'), ('Stockholm', 'Brussels'), ('Istanbul', 'Munich'), ('Istanbul', 'Riga'),
    ('Prague', 'Split'), ('Vienna', 'Brussels'), ('Vienna', 'Riga'), ('Split', 'Stockholm'),
    ('Munich', 'Amsterdam'), ('Split', 'Amsterdam'), ('Amsterdam', 'Stockholm'), ('Amsterdam', 'Riga'),
    ('Vienna', 'Stockholm'), ('Vienna', 'Istanbul'), ('Vienna', 'Seville'), ('Istanbul', 'Amsterdam'),
    ('Munich', 'Brussels'), ('Prague', 'Munich'), ('Riga', 'Munich'), ('Prague', 'Amsterdam'),
    ('Prague', 'Brussels'), ('Prague', 'Istanbul'), ('Istanbul', 'Stockholm'), ('Vienna', 'Prague'),
    ('Munich', 'Split'), ('Vienna', 'Amsterdam'), ('Prague', 'Stockholm'), ('Brussels', 'Seville'),
    ('Munich', 'Stockholm'), ('Istanbul', 'Brussels'), ('Amsterdam', 'Seville'), ('Vienna', 'Split'),
    ('Munich', 'Seville'), ('Riga', 'Brussels'), ('Prague', 'Riga'), ('Vienna', 'Munich')
]

# Convert city names to indices for easier handling
city_indices = {
    'Prague': 0, 'Brussels': 1, 'Riga': 2, 'Munich': 3, 'Seville': 4,
    'Stockholm': 5, 'Istanbul': 6, 'Amsterdam': 7, 'Vienna': 8, 'Split': 9
}

# Add flight constraints
starts = [prague_start, brussels_start, riga_start, munich_start, seville_start,
          stockholm_start, istanbul_start, amsterdam_start, vienna_start, split_start]
durations = [prague_duration, brussels_duration, riga_duration, munich_duration, seville_duration,
             stockholm_duration, istanbul_duration, amsterdam_duration, vienna_duration, split_duration]

for i in range(len(cities)):
    for j in range(i + 1, len(cities)):
        if (cities[i], cities[j]) in possible_flights or (cities[j], cities[i]) in possible_flights:
            add_flight_constraints(solver, starts[i], durations[i], starts[j], durations[j], possible_flights)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i, city in enumerate(cities):
        start_day = model[starts[i]].as_long()
        end_day = start_day + durations[i] - 1
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        if end_day != start_day:
            itinerary.append({"day_range": f"Day {end_day}", "place": city})
    # Sort the itinerary by day
    itinerary.sort(key=lambda x: int(x["day_range"].split('-')[0].split()[1]))
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")