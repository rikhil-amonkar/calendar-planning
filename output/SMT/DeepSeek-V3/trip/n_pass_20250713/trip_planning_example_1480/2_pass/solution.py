from z3 import *
import json

# Define the cities
cities = [
    "Geneva", "Istanbul", "Vienna", "Riga", "Brussels", "Madrid",
    "Vilnius", "Venice", "Munich", "Reykjavik"
]

# Direct flights: a list of tuples (from, to)
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

# Create a dictionary to map city names to indices for easier handling
city_index = {city: idx for idx, city in enumerate(cities)}

# Create a connectivity matrix: can we fly directly from city A to city B?
connectivity = [[False for _ in cities] for _ in cities]
for from_city, to_city in direct_flights:
    from_idx = city_index[from_city]
    to_idx = city_index[to_city]
    connectivity[from_idx][to_idx] = True
    connectivity[to_idx][from_idx] = True  # flights are bidirectional

# Z3 solver setup
s = Solver()

# Variables: for each day (1..27), which city are we in?
day_city = [Int(f"day_{day}_city") for day in range(1, 28)]  # days 1..27

# Each day's city must be a valid city index (0..9)
for day in range(27):
    s.add(day_city[day] >= 0, day_city[day] < len(cities))

# Connectivity constraints: if we change cities between day i and i+1, there must be a direct flight
for day in range(26):  # days 1..26 vs 2..27
    current_city = day_city[day]
    next_city = day_city[day + 1]
    s.add(Or(current_city == next_city,
           And(current_city != next_city,
               connectivity[current_city][next_city])))

# Fixed constraints:
# Geneva between day 1 and 4 (days 1-4, indices 0-3)
for day in range(4):
    s.add(day_city[day] == city_index["Geneva"])

# Venice workshop between day 7 and 11 (days 7-11, indices 6-10)
for day in range(6, 11):
    s.add(day_city[day] == city_index["Venice"])

# Vilnius friends between day 20 and 23 (days 20-23, indices 19-22)
for day in range(19, 23):
    s.add(day_city[day] == city_index["Vilnius"])

# Brussels wedding between day 26 and 27 (days 26-27, indices 25-26)
for day in range(25, 27):
    s.add(day_city[day] == city_index["Brussels"])

# Duration constraints:
# Istanbul: 4 days
s.add(Sum([If(day_city[day] == city_index["Istanbul"], 1, 0) for day in range(27)]) == 4)
# Vienna: 4 days
s.add(Sum([If(day_city[day] == city_index["Vienna"], 1, 0) for day in range(27)]) == 4)
# Riga: 2 days
s.add(Sum([If(day_city[day] == city_index["Riga"], 1, 0) for day in range(27)]) == 2)
# Brussels: 2 days (wedding days 26-27 are 2 days)
s.add(Sum([If(day_city[day] == city_index["Brussels"], 1, 0) for day in range(27)]) == 2)
# Madrid: 4 days
s.add(Sum([If(day_city[day] == city_index["Madrid"], 1, 0) for day in range(27)]) == 4)
# Vilnius: 4 days (friends days 20-23 are 4 days)
s.add(Sum([If(day_city[day] == city_index["Vilnius"], 1, 0) for day in range(27)]) == 4)
# Venice: 5 days (workshop days 7-11 are 5 days)
s.add(Sum([If(day_city[day] == city_index["Venice"], 1, 0) for day in range(27)]) == 5)
# Geneva: 4 days (days 1-4 are 4 days)
s.add(Sum([If(day_city[day] == city_index["Geneva"], 1, 0) for day in range(27)]) == 4)
# Munich: 5 days
s.add(Sum([If(day_city[day] == city_index["Munich"], 1, 0) for day in range(27)]) == 5)
# Reykjavik: 2 days
s.add(Sum([If(day_city[day] == city_index["Reykjavik"], 1, 0) for day in range(27)]) == 2)

# Check if the problem is satisfiable
if s.check() == sat:
    model = s.model()
    day_plan = []
    for day in range(27):
        city_idx = model.eval(day_city[day]).as_long()
        day_plan.append(cities[city_idx])
    
    itinerary = []
    i = 0
    while i < 27:
        current_city = day_plan[i]
        start_day = i + 1  # days are 1-based
        j = i + 1
        while j < 27 and day_plan[j] == current_city:
            j += 1
        end_day = j  # days are 1-based, so the range is start_day to end_day
        
        if start_day == end_day:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
        
        if j < 27:
            next_city = day_plan[j]
            # Add the flight day for both cities
            itinerary.append({"day_range": f"Day {j}", "place": current_city})
            itinerary.append({"day_range": f"Day {j}", "place": next_city})
        
        i = j
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No valid itinerary found.")