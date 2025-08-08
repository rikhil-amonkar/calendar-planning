from z3 import *

# Mapping of cities to integers
city_mapping = {
    "Lisbon": 0,
    "Dubrovnik": 1,
    "Copenhagen": 2,
    "Prague": 3,
    "Stockholm": 4,
    "Split": 5,
    "Tallinn": 10,
    "Lyon": 11
}
reverse_mapping = {v: k for k, v in city_mapping.items()}

# Required days for each city (for intermediate cities: indices 0-5)
days_list = [2, 5, 5, 3, 4, 3]  # Lisbon, Dubrovnik, Copenhagen, Prague, Stockholm, Split

# Flight edges as integer pairs
flight_edges = [
    ("Dubrovnik", "Stockholm"),
    ("Lisbon", "Copenhagen"),
    ("Lisbon", "Lyon"),
    ("Copenhagen", "Stockholm"),
    ("Copenhagen", "Split"),
    ("Prague", "Stockholm"),
    ("Tallinn", "Stockholm"),
    ("Tallinn", "Copenhagen"),
    ("Tallinn", "Prague"),
    ("Prague", "Lyon"),
    ("Lisbon", "Stockholm"),
    ("Prague", "Lisbon"),
    ("Stockholm", "Split"),
    ("Prague", "Copenhagen"),
    ("Split", "Lyon"),
    ("Copenhagen", "Dubrovnik"),
    ("Prague", "Split")
]

# Convert flight edges to integer pairs
flight_edges_int = []
for a, b in flight_edges:
    flight_edges_int.append((city_mapping[a], city_mapping[b]))

# Create Z3 variables for the 6 intermediate cities (positions 2 to 7)
c2, c3, c4, c5, c6, c7 = Ints('c2 c3 c4 c5 c6 c7')

# Define the days for each intermediate city using If expressions
def get_days(city_var):
    return If(city_var == 0, 2, 
           If(city_var == 1, 5,
           If(city_var == 2, 5,
           If(city_var == 3, 3,
           If(city_var == 4, 4, 3)))))  # 5: Split -> 3

d2 = get_days(c2)
d3 = get_days(c3)
d4 = get_days(c4)
d5 = get_days(c5)
d6 = get_days(c6)
d7 = get_days(c7)

# Compute start and end days for each intermediate city
s2 = 2
e2 = s2 + d2 - 1  # = 1 + d2

s3 = e2
e3 = s3 + d3 - 1  # = d2 + d3

s4 = e3
e4 = s4 + d4 - 1  # = d2 + d3 + d4 - 1

s5 = e4
e5 = s5 + d5 - 1  # = d2 + d3 + d4 + d5 - 2

s6 = e5
e6 = s6 + d6 - 1  # = d2 + d3 + d4 + d5 + d6 - 3

s7 = e6
e7 = s7 + d7 - 1  # = d2 + d3 + d4 + d5 + d6 + d7 - 4

# Event constraints
lisbon_constraint = Or(
    And(c3 == 0, s3 <= 5, e3 >= 4),
    And(c4 == 0, s4 <= 5, e4 >= 4),
    And(c5 == 0, s5 <= 5, e5 >= 4),
    And(c6 == 0, s6 <= 5, e6 >= 4)
)

stockholm_constraint = Or(
    And(c3 == 4, s3 <= 16, e3 >= 13),
    And(c4 == 4, s4 <= 16, e4 >= 13),
    And(c5 == 4, s5 <= 16, e5 >= 13),
    And(c6 == 4, s6 <= 16, e6 >= 13),
    And(c7 == 4, s7 <= 16, e7 >= 13)  # e7 is 18, so >=13 is true
)

# Flight constraint helper function
def flight_cons(a, b):
    return Or([Or(And(a == a_val, b == b_val), And(a == b_val, b == a_val)]) 
              for (a_val, b_val) in flight_edges_int])

s = Solver()

# Distinct and range constraints for intermediate cities
s.add(Distinct(c2, c3, c4, c5, c6, c7))
for var in [c2, c3, c4, c5, c6, c7]:
    s.add(Or([var == i for i in range(6)]))

# Event constraints
s.add(lisbon_constraint)
s.add(stockholm_constraint)

# Flight constraints
s.add(flight_cons(10, c2))       # Tallinn to first intermediate
s.add(flight_cons(c2, c3))       # between intermediates
s.add(flight_cons(c3, c4))
s.add(flight_cons(c4, c5))
s.add(flight_cons(c5, c6))
s.add(flight_cons(c6, c7))
s.add(flight_cons(c7, 11))       # last intermediate to Lyon

# Check and get model
if s.check() == sat:
    model = s.model()
    # Get values for intermediate cities
    c2_val = model.eval(c2).as_long()
    c3_val = model.eval(c3).as_long()
    c4_val = model.eval(c4).as_long()
    c5_val = model.eval(c5).as_long()
    c6_val = model.eval(c6).as_long()
    c7_val = model.eval(c7).as_long()
    
    # Get the actual days for each intermediate city
    def get_actual_days(city_val):
        return days_list[city_val]
    
    d2_val = get_actual_days(c2_val)
    d3_val = get_actual_days(c3_val)
    d4_val = get_actual_days(c4_val)
    d5_val = get_actual_days(c5_val)
    d6_val = get_actual_days(c6_val)
    d7_val = get_actual_days(c7_val)
    
    # Compute the intervals for each city
    # Tallinn: [1,2]
    # Lyon: [18,19]
    # Intermediates:
    s2_val = 2
    e2_val = s2_val + d2_val - 1
    
    s3_val = e2_val
    e3_val = s3_val + d3_val - 1
    
    s4_val = e3_val
    e4_val = s4_val + d4_val - 1
    
    s5_val = e4_val
    e5_val = s5_val + d5_val - 1
    
    s6_val = e5_val
    e6_val = s6_val + d6_val - 1
    
    s7_val = e6_val
    e7_val = s7_val + d7_val - 1  # should be 18
    
    # Map the city integers to names
    cities = [reverse_mapping[i] for i in [c2_val, c3_val, c4_val, c5_val, c6_val, c7_val]]
    intervals = {
        "Tallinn": (1, 2),
        cities[0]: (s2_val, e2_val),
        cities[1]: (s3_val, e3_val),
        cities[2]: (s4_val, e4_val),
        cities[3]: (s5_val, e5_val),
        cities[4]: (s6_val, e6_val),
        cities[5]: (s7_val, e7_val),
        "Lyon": (18, 19)
    }
    
    # Generate the itinerary as a list of day-city entries
    itinerary = []
    for day in range(1, 20):
        for city, (start, end) in intervals.items():
            if day >= start and day <= end:
                itinerary.append({"day": day, "city": city})
    
    # Output as JSON
    import json
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result, indent=2))
else:
    print("No solution found")