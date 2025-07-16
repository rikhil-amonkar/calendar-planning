from z3 import *
import json

# Define cities with consistent spelling
cities = [
    "Geneva", "Istanbul", "Vienna", "Riga", "Brussels", "Madrid",
    "Vilnius", "Venice", "Munich", "Reykjavik"
]

# Corrected direct flights (bidirectional)
direct_flights = [
    ("Munich", "Vienna"), ("Istanbul", "Brussels"), ("Vienna", "Vilnius"),
    ("Madrid", "Munich"), ("Venice", "Brussels"), ("Riga", "Brussels"),
    ("Geneva", "Istanbul"), ("Munich", "Reykjavik"), ("Vienna", "Istanbul"),
    ("Riga", "Istanbul"), ("Reykjavik", "Vienna"), ("Venice", "Munich"),
    ("Madrid", "Venice"), ("Vilnius", "Istanbul"), ("Venice", "Vienna"),
    ("Venice", "Istanbul"), ("Reykjavik", "Madrid"), ("Riga", "Munich"),
    ("Munich", "Istanbul"), ("Reykjavik", "Brussels"), ("Vilnius", "Brussels"),
    ("Vilnius", "Munich"), ("Madrid", "Vienna"), ("Vienna", "Riga"),
    ("Geneva", "Vienna"), ("Geneva", "Brussels"), ("Geneva", "Madrid"),
    ("Munich", "Brussels"), ("Madrid", "Istanbul"), ("Geneva", "Munich"),
    ("Riga", "Vilnius")
]

# Create city index mapping
city_index = {city: idx for idx, city in enumerate(cities)}

# Build connectivity matrix
connectivity = [[False]*len(cities) for _ in cities]
for from_city, to_city in direct_flights:
    from_idx = city_index[from_city]
    to_idx = city_index[to_city]
    connectivity[from_idx][to_idx] = True
    connectivity[to_idx][from_idx] = True

# Initialize solver
s = Solver()

# Day variables (1-27)
day_city = [Int(f"day_{day}") for day in range(1, 28)]

# Each day must be a valid city
for day in range(27):
    s.add(day_city[day] >= 0, day_city[day] < len(cities))

# Flight connectivity constraints
for day in range(26):
    current = day_city[day]
    next_ = day_city[day+1]
    s.add(Or(current == next_, 
           Or([And(current == i, next_ == j) 
              for i in range(len(cities)) 
              for j in range(len(cities)) 
              if connectivity[i][j]])))

# Fixed constraints
for day in range(4):  # Geneva days 1-4
    s.add(day_city[day] == city_index["Geneva"])

for day in range(6, 11):  # Venice days 7-11
    s.add(day_city[day] == city_index["Venice"])

for day in range(19, 23):  # Vilnius days 20-23
    s.add(day_city[day] == city_index["Vilnius"])

for day in range(25, 27):  # Brussels days 26-27
    s.add(day_city[day] == city_index["Brussels"])

# Duration constraints
duration_requirements = {
    "Istanbul": 4,
    "Vienna": 4,
    "Riga": 2,
    "Brussels": 2,  # Already fixed days 26-27
    "Madrid": 4,
    "Vilnius": 4,   # Already fixed days 20-23
    "Venice": 5,     # Already fixed days 7-11
    "Geneva": 4,     # Already fixed days 1-4
    "Munich": 5,
    "Reykjavik": 2
}

for city, days in duration_requirements.items():
    s.add(Sum([If(day_city[d] == city_index[city], 1, 0) for d in range(27)]) == days)

# Solve
if s.check() == sat:
    model = s.model()
    day_plan = [cities[model.eval(day_city[d]).as_long()] for d in range(27)]
    
    # Build itinerary
    itinerary = []
    current = day_plan[0]
    start = 1
    for day in range(1, 27):
        if day_plan[day] == current:
            continue
        # Add stay
        if start == day:
            itinerary.append({"day_range": f"Day {start}", "place": current})
        else:
            itinerary.append({"day_range": f"Day {start}-{day}", "place": current})
        # Add flight day
        itinerary.append({"day_range": f"Day {day}", "place": current})
        itinerary.append({"day_range": f"Day {day}", "place": day_plan[day]})
        current = day_plan[day]
        start = day + 1
    
    # Add final stay
    if start <= 27:
        if start == 27:
            itinerary.append({"day_range": f"Day {start}", "place": current})
        else:
            itinerary.append({"day_range": f"Day {start}-27", "place": current})
    
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No valid itinerary found.")