from z3 import *
import json

# Define the city enumeration
City, (warsaw, budapest, paris, riga) = EnumSort('City', ['Warsaw', 'Budapest', 'Paris', 'Riga'])

# Create a mapping from Z3 constants to city names
city_names = {
    warsaw: "Warsaw",
    budapest: "Budapest",
    paris: "Paris",
    riga: "Riga"
}

# Define direct flight edges
edges = [
    (warsaw, budapest),
    (warsaw, riga),
    (budapest, paris),
    (warsaw, paris),
    (paris, riga)
]

# Initialize the solver
s = Solver()

# Create arrays for start_city and end_city for days 1 to 17
start_city = [None]  # index 0 unused
end_city = [None]    # index 0 unused

for i in range(1, 18):
    start_city.append(Const(f'start_city_{i}', City))
    end_city.append(Const(f'end_city_{i}', City))

# Constraint: Start in Warsaw on day 1
s.add(start_city[1] == warsaw)

# Constraint: End city of day i is start city of day i+1 for i=1 to 16
for i in range(1, 17):
    s.add(end_city[i] == start_city[i+1])

# Constraint: Must be in Warsaw on day 1 and day 2
s.add(Or(start_city[1] == warsaw, end_city[1] == warsaw))
s.add(Or(start_city[2] == warsaw, end_city[2] == warsaw))

# Flight constraint: If start and end cities differ, there must be a direct flight
for i in range(1, 18):
    cond = (start_city[i] != end_city[i])
    flight_ok = Or([Or(And(start_city[i] == a, end_city[i] == b), And(start_city[i] == b, end_city[i] == a)) for (a, b) in edges])
    s.add(Implies(cond, flight_ok))

# Function to check if a day i is in city c
def in_city(i, c):
    return Or(start_city[i] == c, end_city[i] == c)

# Total days per city
total_riga = Sum([If(in_city(i, riga), 1, 0) for i in range(1, 18)])
total_budapest = Sum([If(in_city(i, budapest), 1, 0) for i in range(1, 18)])
total_paris = Sum([If(in_city(i, paris), 1, 0) for i in range(1, 18)])
total_warsaw = Sum([If(in_city(i, warsaw), 1, 0) for i in range(1, 18)])

s.add(total_riga == 7)
s.add(total_budapest == 7)
s.add(total_paris == 4)
s.add(total_warsaw == 2)

# Constraint: At least one day in Riga between days 11 and 17
s.add(Or([in_city(i, riga) for i in range(11, 18)]))

# Check for a solution
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(1, 18):
        start_val = model.eval(start_city[i])
        end_val = model.eval(end_city[i])
        start_str = city_names[start_val]
        end_str = city_names[end_val]
        if start_str == end_str:
            cities = [start_str]
        else:
            cities = sorted([start_str, end_str])
        itinerary.append({"day": i, "city": cities})
    
    result = {'itinerary': itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")