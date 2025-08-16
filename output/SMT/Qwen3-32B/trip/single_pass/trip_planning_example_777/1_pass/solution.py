from z3 import *
import json

# Define the cities as an EnumSort
Cities, (Dublin, Helsinki, Riga, Reykjavik, Vienna, Tallinn) = EnumSort('Cities', ['Dublin', 'Helsinki', 'Riga', 'Reykjavik', 'Vienna', 'Tallinn'])

# Create the sequence variables
seq = [Const(f'seq_{i}', Cities) for i in range(6)]

# Solver instance
s = Solver()

# All cities are distinct in the sequence
s.add(Distinct(seq))

# Define start and end days for each position in the sequence
start_days = [Int(f'start_{i}') for i in range(6)]
end_days = [Int(f'end_{i}') for i in range(6)]

# Constraints for start and end days
s.add(start_days[0] == 1)
for i in range(1, 6):
    s.add(start_days[i] == end_days[i-1])

for i in range(6):
    # Compute duration based on city
    d = If(seq[i] == Dublin, 5,
        If(seq[i] == Helsinki, 3,
            If(seq[i] == Riga, 3,
                If(seq[i] == Reykjavik, 2,
                    If(seq[i] == Vienna, 2,
                        If(seq[i] == Tallinn, 5, 0)
                    )
                )
            )
        )
    )
    s.add(end_days[i] == start_days[i] + d - 1)

# End day of last city is 15
s.add(end_days[5] == 15)

# Constraints for fixed start days of certain cities
for i in range(6):
    # Helsinki's start day is 3
    s.add(Implies(seq[i] == Helsinki, start_days[i] == 3))
    # Vienna's start day is 2
    s.add(Implies(seq[i] == Vienna, start_days[i] == 2))
    # Tallinn's start day is 7
    s.add(Implies(seq[i] == Tallinn, start_days[i] == 7))

# Direct flights between consecutive cities
direct_flights = {
    (Helsinki, Riga),
    (Riga, Helsinki),
    (Riga, Tallinn),
    (Tallinn, Riga),
    (Vienna, Helsinki),
    (Helsinki, Vienna),
    (Riga, Dublin),
    (Dublin, Riga),
    (Vienna, Riga),
    (Riga, Vienna),
    (Reykjavik, Vienna),
    (Vienna, Reykjavik),
    (Helsinki, Dublin),
    (Dublin, Helsinki),
    (Tallinn, Dublin),
    (Dublin, Tallinn),
    (Reykjavik, Helsinki),
    (Helsinki, Reykjavik),
    (Reykjavik, Dublin),
    (Dublin, Reykjavik),
    (Helsinki, Tallinn),
    (Tallinn, Helsinki),
    (Vienna, Dublin),
    (Dublin, Vienna),
}

for i in range(5):
    current = seq[i]
    next_city = seq[i+1]
    allowed = []
    for a, b in direct_flights:
        allowed.append(And(current == a, next_city == b))
    s.add(Or(allowed))

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    # Extract the sequence of cities and their start/end days
    cities_seq = [model.eval(seq[i]) for i in range(6)]
    start_days_values = [model.eval(start_days[i]).as_long() for i in range(6)]
    end_days_values = [model.eval(end_days[i]).as_long() for i in range(6)]
    
    # Build the itinerary
    itinerary = []
    for day in range(1, 16):
        for i in range(6):
            if start_days_values[i] <= day <= end_days_values[i]:
                city_name = cities_seq[i].decl().name()
                itinerary.append({"day": day, "city": city_name})
                break
    
    # Print the JSON-formatted output
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")