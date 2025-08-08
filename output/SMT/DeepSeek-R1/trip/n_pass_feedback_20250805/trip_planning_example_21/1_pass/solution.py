from z3 import *
import json

# Define the variables
flight_day1 = Int('flight_day1')
flight_day2 = Int('flight_day2')
city1 = Int('city1')
city2 = Int('city2')
city3 = Int('city3')

s = Solver()

# The chain must be either (0,1,2) for (Mykonos, Vienna, Venice) or (2,1,0) for (Venice, Vienna, Mykonos)
s.add(Or(
    And(city1 == 0, city2 == 1, city3 == 2),
    And(city1 == 2, city2 == 1, city3 == 0)
))

s.add(flight_day1 >= 1, flight_day1 < flight_day2, flight_day2 <= 10)

# Days for each city
mykonos_days = If(city1 == 0, flight_day1, 0) + If(city2 == 0, flight_day2 - flight_day1 + 1, 0) + If(city3 == 0, 10 - flight_day2 + 1, 0)
vienna_days = If(city1 == 1, flight_day1, 0) + If(city2 == 1, flight_day2 - flight_day1 + 1, 0) + If(city3 == 1, 10 - flight_day2 + 1, 0)
venice_days = If(city1 == 2, flight_day1, 0) + If(city2 == 2, flight_day2 - flight_day1 + 1, 0) + If(city3 == 2, 10 - flight_day2 + 1, 0)

s.add(mykonos_days == 2)
s.add(vienna_days == 4)
s.add(venice_days == 6)

# Workshop constraint: 
s.add(If(city1 == 2, flight_day1 >= 5, True))
s.add(If(city2 == 2, flight_day2 >= 5, True))

if s.check() == sat:
    m = s.model()
    fd1 = m[flight_day1].as_long()
    fd2 = m[flight_day2].as_long()
    c1 = m[city1].as_long()
    c2 = m[city2].as_long()
    c3 = m[city3].as_long()
    
    city_map = {0: "Mykonos", 1: "Vienna", 2: "Venice"}
    
    itinerary_list = []
    for day in range(1, 11):
        cities = []
        if day <= fd1:
            cities.append(city_map[c1])
        if day >= fd1 and day <= fd2:
            cities.append(city_map[c2])
        if day >= fd2:
            cities.append(city_map[c3])
        for city in cities:
            itinerary_list.append({"day": day, "city": city})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))
else:
    print(json.dumps({"itinerary": []}))