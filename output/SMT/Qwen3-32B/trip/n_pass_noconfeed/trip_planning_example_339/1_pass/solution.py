import z3
import json

# Define city codes
WARS = 0
RIGA = 1
BUDA = 2
PARIS = 3

# Allowed direct flights (both directions)
allowed_pairs = [
    (WARS, BUDA),
    (BUDA, WARS),
    (WARS, RIGA),
    (RIGA, WARS),
    (BUDA, PARIS),
    (PARIS, BUDA),
    (WARS, PARIS),
    (PARIS, WARS),
    (PARIS, RIGA),
    (RIGA, PARIS),
]

# Create Z3 solver
solver = z3.Solver()

# Create variables for the sequence of cities
c1, c2, c3, c4 = [z3.Int(f'c{i}') for i in range(1, 5)]

# Add constraints
solver.add(z3.Distinct(c1, c2, c3, c4))
solver.add(c1 == WARS)

# Helper function to add flight constraints
def add_flight_constraint(prev, next_city):
    constraints = []
    for (a, b) in allowed_pairs:
        constraints.append(z3.And(prev == a, next_city == b))
    solver.add(z3.Or(*constraints))

# Add flight constraints between consecutive cities
add_flight_constraint(c1, c2)
add_flight_constraint(c2, c3)
add_flight_constraint(c3, c4)

# Calculate durations for each segment
def get_duration(city_code):
    return z3.If(city_code == WARS, 2,
        z3.If(city_code == RIGA, 7,
            z3.If(city_code == BUDA, 7, 4)))

d1 = get_duration(c1)
d2 = get_duration(c2)
d3 = get_duration(c3)
d4 = get_duration(c4)

# Calculate start and end days for each segment
start_1 = 1
end_1 = start_1 + d1 - 1

start_2 = end_1
end_2 = start_2 + d2 - 1

start_3 = end_2
end_3 = start_3 + d3 - 1

start_4 = end_3
end_4 = start_4 + d4 - 1

# Add wedding constraint for Riga
solver.add(z3.Or(
    z3.And(c1 == RIGA, start_1 <= 17, end_1 >= 11),
    z3.And(c2 == RIGA, start_2 <= 17, end_2 >= 11),
    z3.And(c3 == RIGA, start_3 <= 17, end_3 >= 11),
    z3.And(c4 == RIGA, start_4 <= 17, end_4 >= 11)
))

# Check if the solver can find a solution
if solver.check() == z3.sat:
    model = solver.model()
    # Extract the cities in the sequence
    cities_seq = [model.eval(c1).as_long(), model.eval(c2).as_long(), model.eval(c3).as_long(), model.eval(c4).as_long()]
    # Map to city names
    city_names = {0: "Warsaw", 1: "Riga", 2: "Budapest", 3: "Paris"}
    cities_str = [city_names[code] for code in cities_seq]
    
    # Calculate the actual start and end days for each segment
    d1_val = 2 if cities_seq[0] == WARS else (7 if cities_seq[0] == RIGA else (7 if cities_seq[0] == BUDA else 4))
    d2_val = 2 if cities_seq[1] == WARS else (7 if cities_seq[1] == RIGA else (7 if cities_seq[1] == BUDA else 4))
    d3_val = 2 if cities_seq[2] == WARS else (7 if cities_seq[2] == RIGA else (7 if cities_seq[2] == BUDA else 4))
    d4_val = 2 if cities_seq[3] == WARS else (7 if cities_seq[3] == RIGA else (7 if cities_seq[3] == BUDA else 4))
    
    # Compute start and end days
    start_1_val = 1
    end_1_val = start_1_val + d1_val - 1
    
    start_2_val = end_1_val
    end_2_val = start_2_val + d2_val - 1
    
    start_3_val = end_2_val
    end_3_val = start_3_val + d3_val - 1
    
    start_4_val = end_3_val
    end_4_val = start_4_val + d4_val - 1
    
    # Create the itinerary
    itinerary = []
    for i in range(4):
        start = [start_1_val, start_2_val, start_3_val, start_4_val][i]
        end = [end_1_val, end_2_val, end_3_val, end_4_val][i]
        city = cities_str[i]
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))