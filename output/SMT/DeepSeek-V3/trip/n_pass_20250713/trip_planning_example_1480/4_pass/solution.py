from z3 import *
import json

# Define the cities with correct spelling
cities = [
    "Geneva", "Istanbul", "Vienna", "Riga", "Brussels", "Madrid",
    "Vilnius", "Venice", "Munich", "Reykjavik"
]

# Corrected direct flights list
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

# Create connectivity matrix
connectivity = [[False for _ in cities] for _ in cities]
for from_city, to_city in direct_flights:
    from_idx = city_index[from_city]
    to_idx = city_index[to_city]
    connectivity[from_idx][to_idx] = True
    connectivity[to_idx][from_idx] = True  # flights are bidirectional

# Z3 solver setup
s = Solver()

# Variables: for each day (1..27), which city are we in?
day_city = [Int(f"day_{day}_city") for day in range(1, 28)]

# Each day's city must be a valid city index (0..9)
for day in range(27):
    s.add(day_city[day] >= 0, day_city[day] < len(cities))

# Connectivity constraints
for day in range(26):
    current = day_city[day]
    next_ = day_city[day + 1]
    s.add(Or(current == next_,
           Or([And(current == i, next_ == j)
              for i in range(len(cities))
              for j in range(len(cities))
              if connectivity[i][j]])))

# Fixed constraints
# Geneva days 1-4
for day in range(4):
    s.add(day_city[day] == city_index["Geneva"])

# Venice days 7-11
for day in range(6, 11):
    s.add(day_city[day] == city_index["Venice"])

# Vilnius days 20-23
for day in range(19, 23):
    s.add(day_city[day] == city_index["Vilnius"])

# Brussels days 26-27
for day in range(25, 27):
    s.add(day_city[day] == city_index["Brussels"])

# Duration constraints
s.add(Sum([If(day_city[day] == city_index["Istanbul"], 1, 0) for day in range(27)]) == 4)
s.add(Sum([If(day_city[day] == city_index["Vienna"], 1, 0) for day in range(27)]) == 4)
s.add(Sum([If(day_city[day] == city_index["Riga"], 1, 0) for day in range(27)]) == 2)
s.add(Sum([If(day_city[day] == city_index["Brussels"], 1, 0) for day in range(27)]) == 2)
s.add(Sum([If(day_city[day] == city_index["Madrid"], 1, 0) for day in range(27)]) == 4)
s.add(Sum([If(day_city[day] == city_index["Vilnius"], 1, 0) for day in range(27)]) == 4)
s.add(Sum([If(day_city[day] == city_index["Venice"], 1, 0) for day in range(27)]) == 5)
s.add(Sum([If(day_city[day] == city_index["Geneva"], 1, 0) for day in range(27)]) == 4)
s.add(Sum([If(day_city[day] == city_index["Munich"], 1, 0) for day in range(27)]) == 5)
s.add(Sum([If(day_city[day] == city_index["Reykjavik"], 1, 0) for day in range(27)]) == 2)

# Check if satisfiable
if s.check() == sat:
    model = s.model()
    day_plan = []
    for day in range(27):
        city_idx = model.eval(day_city[day]).as_long()
        day_plan.append(cities[city_idx])
    
    # Build itinerary
    itinerary = []
    current_city = day_plan[0]
    start_day = 1
    for day in range(1, 27):
        if day_plan[day] == current_city:
            continue
        else:
            end_day = day
            if start_day == end_day:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
            # Add flight day
            itinerary.append({"day_range": f"Day {day}", "place": current_city})
            itinerary.append({"day_range": f"Day {day}", "place": day_plan[day]})
            current_city = day_plan[day]
            start_day = day + 1
    
    # Add last stay
    if start_day <= 27:
        if start_day == 27:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-27", "place": current_city})
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No valid itinerary found.")