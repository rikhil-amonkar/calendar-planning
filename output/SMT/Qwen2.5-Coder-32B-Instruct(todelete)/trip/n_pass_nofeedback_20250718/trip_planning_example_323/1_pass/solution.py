from z3 import *

# Define the solver
solver = Solver()

# Define the variables for the start day of each city
start_split = Int('start_split')
start_oslo = Int('start_oslo')
start_london = Int('start_london')
start_porto = Int('start_porto')

# Define the duration of stay in each city
duration_split = 5
duration_oslo = 2
duration_london = 7
duration_porto = 5

# Define the constraints
# Total trip duration is 16 days
solver.add(start_split + duration_split <= 16)
solver.add(start_oslo + duration_oslo <= 16)
solver.add(start_london + duration_london <= 16)
solver.add(start_porto + duration_porto <= 16)

# Stay in Split from day 7 to day 11
solver.add(start_split <= 6)
solver.add(start_split + duration_split >= 11)

# Visit relatives in London between day 1 and day 7
solver.add(start_london <= 6)
solver.add(start_london + duration_london >= 1)

# Direct flights constraints
# London and Oslo
solver.add(Or(start_oslo >= start_london + duration_london, start_london >= start_oslo + duration_oslo))
# Split and Oslo
solver.add(Or(start_oslo >= start_split + duration_split, start_split >= start_oslo + duration_oslo))
# Oslo and Porto
solver.add(Or(start_porto >= start_oslo + duration_oslo, start_oslo >= start_porto + duration_porto))
# London and Split
solver.add(Or(start_split >= start_london + duration_london, start_london >= start_split + duration_split))

# Ensure no overlap in days between cities
solver.add(Or(start_oslo >= start_london + duration_london, start_london >= start_oslo + duration_oslo))
solver.add(Or(start_split >= start_oslo + duration_oslo, start_oslo >= start_split + duration_split))
solver.add(Or(start_porto >= start_oslo + duration_oslo, start_oslo >= start_porto + duration_porto))
solver.add(Or(start_split >= start_london + duration_london, start_london >= start_split + duration_split))
solver.add(Or(start_porto >= start_london + duration_london, start_london >= start_porto + duration_porto))
solver.add(Or(start_porto >= start_split + duration_split, start_split >= start_porto + duration_porto))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    itinerary.append({'day': model[start_split].as_long(), 'city': 'Split'})
    itinerary.append({'day': model[start_oslo].as_long(), 'city': 'Oslo'})
    itinerary.append({'day': model[start_london].as_long(), 'city': 'London'})
    itinerary.append({'day': model[start_porto].as_long(), 'city': 'Porto'})

    # Sort the itinerary by day
    itinerary.sort(key=lambda x: x['day'])

    # Create the final JSON output
    final_itinerary = []
    for i in range(len(itinerary)):
        city = itinerary[i]['city']
        start_day = itinerary[i]['day']
        if i < len(itinerary) - 1:
            end_day = itinerary[i + 1]['day'] + duration_porto - 1 if city == 'Porto' else itinerary[i + 1]['day'] - 1
        else:
            end_day = start_day + (duration_split if city == 'Split' else duration_oslo if city == 'Oslo' else duration_london if city == 'London' else duration_porto) - 1
        final_itinerary.append({'day': f"{start_day}-{end_day}", 'city': city})

    print({"itinerary": final_itinerary})
else:
    print("No solution found")