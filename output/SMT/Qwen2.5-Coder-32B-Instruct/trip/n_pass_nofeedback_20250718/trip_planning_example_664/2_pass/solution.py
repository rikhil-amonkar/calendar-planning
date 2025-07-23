from z3 import *

# Define the solver
solver = Solver()

# Define the variables for the start day of each city visit
start_tallinn = Int('start_tallinn')
start_bucharest = Int('start_bucharest')
start_seville = Int('start_seville')
start_stockholm = Int('start_stockholm')
start_munich = Int('start_munich')
start_milan = Int('start_milan')

# Define the duration of stay in each city
duration_tallinn = 2
duration_bucharest = 4
duration_seville = 5
duration_stockholm = 5
duration_munich = 5
duration_milan = 2

# Define the constraints
# Tallinn: 2 days
solver.add(start_tallinn >= 1)
solver.add(start_tallinn + duration_tallinn <= 18)

# Bucharest: 4 days, visit relatives between day 1 and day 4
solver.add(start_bucharest >= 1)
solver.add(start_bucharest + duration_bucharest <= 18)
solver.add(Or(start_bucharest <= 1, start_bucharest + duration_bucharest >= 1))
solver.add(Or(start_bucharest <= 4, start_bucharest + duration_bucharest >= 4))

# Seville: 5 days, meet friends between day 8 and day 12
solver.add(start_seville >= 1)
solver.add(start_seville + duration_seville <= 18)
solver.add(Or(start_seville <= 8, start_seville + duration_seville >= 8))
solver.add(Or(start_seville <= 12, start_seville + duration_seville >= 12))

# Stockholm: 5 days
solver.add(start_stockholm >= 1)
solver.add(start_stockholm + duration_stockholm <= 18)

# Munich: 5 days, attend wedding between day 4 and day 8
solver.add(start_munich >= 1)
solver.add(start_munich + duration_munich <= 18)
solver.add(Or(start_munich <= 4, start_munich + duration_munich >= 4))
solver.add(Or(start_munich <= 8, start_munich + duration_munich >= 8))

# Milan: 2 days
solver.add(start_milan >= 1)
solver.add(start_milan + duration_milan <= 18)

# Direct flight constraints
# Tallinn to Stockholm
solver.add(Or(start_stockholm >= start_tallinn + duration_tallinn, start_tallinn >= start_stockholm + duration_stockholm))

# Bucharest to Munich
solver.add(Or(start_munich >= start_bucharest + duration_bucharest, start_bucharest >= start_munich + duration_munich))

# Munich to Seville
solver.add(Or(start_seville >= start_munich + duration_munich, start_munich >= start_seville + duration_seville))

# Munich to Stockholm
solver.add(Or(start_stockholm >= start_munich + duration_munich, start_munich >= start_stockholm + duration_stockholm))

# Munich to Milan
solver.add(Or(start_milan >= start_munich + duration_munich, start_munich >= start_milan + duration_milan))

# Munich to Tallinn
solver.add(Or(start_tallinn >= start_munich + duration_munich, start_munich >= start_tallinn + duration_tallinn))

# Seville to Milan
solver.add(Or(start_milan >= start_seville + duration_seville, start_seville >= start_milan + duration_milan))

# Milan to Stockholm
solver.add(Or(start_stockholm >= start_milan + duration_milan, start_milan >= start_stockholm + duration_stockholm))

# Ensure no overlap and correct transitions
# Tallinn to Stockholm
solver.add(start_stockholm >= start_tallinn + duration_tallinn - 1)

# Bucharest to Munich
solver.add(start_munich >= start_bucharest + duration_bucharest - 1)

# Munich to Seville
solver.add(start_seville >= start_munich + duration_munich - 1)

# Munich to Stockholm
solver.add(start_stockholm >= start_munich + duration_munich - 1)

# Munich to Milan
solver.add(start_milan >= start_munich + duration_munich - 1)

# Munich to Tallinn
solver.add(start_tallinn >= start_munich + duration_munich - 1)

# Seville to Milan
solver.add(start_milan >= start_seville + duration_seville - 1)

# Milan to Stockholm
solver.add(start_stockholm >= start_milan + duration_milan - 1)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = {
        'itinerary': [
            {'day': model[start_tallinn].as_long(), 'city': 'Tallinn'},
            {'day': model[start_bucharest].as_long(), 'city': 'Bucharest'},
            {'day': model[start_seville].as_long(), 'city': 'Seville'},
            {'day': model[start_stockholm].as_long(), 'city': 'Stockholm'},
            {'day': model[start_munich].as_long(), 'city': 'Munich'},
            {'day': model[start_milan].as_long(), 'city': 'Milan'}
        ]
    }
    # Sort the itinerary by day
    itinerary['itinerary'].sort(key=lambda x: x['day'])
    
    # Create a detailed itinerary with days
    detailed_itinerary = []
    for entry in itinerary['itinerary']:
        start_day = entry['day']
        city = entry['city']
        if city == 'Tallinn':
            end_day = start_day + duration_tallinn - 1
        elif city == 'Bucharest':
            end_day = start_day + duration_bucharest - 1
        elif city == 'Seville':
            end_day = start_day + duration_seville - 1
        elif city == 'Stockholm':
            end_day = start_day + duration_stockholm - 1
        elif city == 'Munich':
            end_day = start_day + duration_munich - 1
        elif city == 'Milan':
            end_day = start_day + duration_milan - 1
        detailed_itinerary.append({'day': f"{start_day}-{end_day}", 'city': city})
    
    print(detailed_itinerary)
else:
    print("No solution found")